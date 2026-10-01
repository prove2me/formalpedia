-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0377Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0377Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:11:53.009548+00:00
-- url     : https://prove2.me/theorems/2769bf57-093f-4700-83cd-a20142eaca34
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0377Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0378Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0377Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0378Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0379Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0380Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0381Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0382Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0383Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0384Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0377Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0378Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0379Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0380Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0381Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0382Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0383Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0384Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0377Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0378Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0379Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0380Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0381Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0382Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0383Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0384Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0377Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0378Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0379Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0380Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0381Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0382Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0383Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0384Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0377Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0377
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

theorem reflection_log_1_neg : (205727137 / 1000000000) ≤ -Real.log (10240 / 12579) ∧
    -Real.log (10240 / 12579) ≤ (102863569 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 22819)) (n := 12)
    (lo := (205727137 / 1000000000)) (hi := (102863569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12579 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12579 / 10240) = 1/(10240 / 12579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (205727137 / 1000000000) (102863569 / 500000000) (Real.log (12579 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12579 / 10240) = -Real.log (10240 / 12579) := by
    rw [show ((12579 / 10240) : ℝ) = ((10240 / 12579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (51862457 / 200000000) ≤ -Real.log (7901 / 10240) ∧
    -Real.log (7901 / 10240) ≤ (129656143 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 18141)) (n := 12)
    (lo := (51862457 / 200000000)) (hi := (129656143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7901) = 1/(7901 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-129656143 / 500000000) (-51862457 / 200000000) (Real.log (7901 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25686077 / 125000000) ≤ -Real.log (320 / 393) ∧
    -Real.log (320 / 393) ≤ (205488617 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 713)) (n := 12)
    (lo := (25686077 / 125000000)) (hi := (205488617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 320) = 1/(320 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25686077 / 125000000) (205488617 / 1000000000) (Real.log (393 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (393 / 320) = -Real.log (320 / 393) := by
    rw [show ((393 / 320) : ℝ) = ((320 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (258932659 / 1000000000) ≤ -Real.log (247 / 320) ∧
    -Real.log (247 / 320) ≤ (12946633 / 50000000) := by
  have h := checkLog_sound (w := (73 / 567)) (n := 12)
    (lo := (258932659 / 1000000000)) (hi := (12946633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 247) = 1/(247 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12946633 / 50000000) (-258932659 / 1000000000) (Real.log (247 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (376266917 / 1000000000) ≤ -Real.log (5120 / 7459) ∧
    -Real.log (5120 / 7459) ≤ (188133459 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 12579)) (n := 12)
    (lo := (376266917 / 1000000000)) (hi := (188133459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7459 / 5120) = 1/(5120 / 7459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (376266917 / 1000000000) (188133459 / 500000000) (Real.log (7459 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7459 / 5120) = -Real.log (5120 / 7459) := by
    rw [show ((7459 / 5120) : ℝ) = ((5120 / 7459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (610343863 / 1000000000) ≤ -Real.log (2781 / 5120) ∧
    -Real.log (2781 / 5120) ≤ (76292983 / 125000000) := by
  have h := checkLog_sound (w := (2339 / 7901)) (n := 12)
    (lo := (610343863 / 1000000000)) (hi := (76292983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2781) = 1/(2781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-76292983 / 125000000) (-610343863 / 1000000000) (Real.log (2781 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (187932319 / 500000000) ≤ -Real.log (160 / 233) ∧
    -Real.log (160 / 233) ≤ (375864639 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 393)) (n := 12)
    (lo := (187932319 / 500000000)) (hi := (375864639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233 / 160) = 1/(160 / 233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (187932319 / 500000000) (375864639 / 1000000000) (Real.log (233 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (233 / 160) = -Real.log (160 / 233) := by
    rw [show ((233 / 160) : ℝ) = ((160 / 233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (19039553 / 31250000) ≤ -Real.log (87 / 160) ∧
    -Real.log (87 / 160) ≤ (609265697 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 87) = 1/(87 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-609265697 / 1000000000) (-19039553 / 31250000) (Real.log (87 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (281931569 / 1000000000) ≤ -Real.log (125000 / 165711) ∧
    -Real.log (125000 / 165711) ≤ (28193157 / 100000000) := by
  have h := checkLog_sound (w := (40711 / 290711)) (n := 12)
    (lo := (281931569 / 1000000000)) (hi := (28193157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165711 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165711 / 125000) = 1/(125000 / 165711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (281931569 / 1000000000) (28193157 / 100000000) (Real.log (165711 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (165711 / 125000) = -Real.log (125000 / 165711) := by
    rw [show ((165711 / 125000) : ℝ) = ((125000 / 165711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (394062367 / 1000000000) ≤ -Real.log (84289 / 125000) ∧
    -Real.log (84289 / 125000) ≤ (12314449 / 31250000) := by
  have h := checkLog_sound (w := (40711 / 209289)) (n := 12)
    (lo := (394062367 / 1000000000)) (hi := (12314449 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84289) = 1/(84289 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-12314449 / 31250000) (-394062367 / 1000000000) (Real.log (84289 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (282254369 / 1000000000) ≤ -Real.log (250000 / 331529) ∧
    -Real.log (250000 / 331529) ≤ (28225437 / 100000000) := by
  have h := checkLog_sound (w := (81529 / 581529)) (n := 12)
    (lo := (282254369 / 1000000000)) (hi := (28225437 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331529 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331529 / 250000) = 1/(250000 / 331529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (282254369 / 1000000000) (28225437 / 100000000) (Real.log (331529 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (331529 / 250000) = -Real.log (250000 / 331529) := by
    rw [show ((331529 / 250000) : ℝ) = ((250000 / 331529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (394697289 / 1000000000) ≤ -Real.log (168471 / 250000) ∧
    -Real.log (168471 / 250000) ≤ (39469729 / 100000000) := by
  have h := checkLog_sound (w := (81529 / 418471)) (n := 12)
    (lo := (394697289 / 1000000000)) (hi := (39469729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 168471) = 1/(168471 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-39469729 / 100000000) (-394697289 / 1000000000) (Real.log (168471 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (212900873 / 1000000000) ≤ -Real.log (500000 / 618631) ∧
    -Real.log (500000 / 618631) ≤ (106450437 / 500000000) := by
  have h := checkLog_sound (w := (118631 / 1118631)) (n := 12)
    (lo := (212900873 / 1000000000)) (hi := (106450437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618631 / 500000) = 1/(500000 / 618631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (212900873 / 1000000000) (106450437 / 500000000) (Real.log (618631 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (618631 / 500000) = -Real.log (500000 / 618631) := by
    rw [show ((618631 / 500000) : ℝ) = ((500000 / 618631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16927543 / 62500000) ≤ -Real.log (381369 / 500000) ∧
    -Real.log (381369 / 500000) ≤ (270840689 / 1000000000) := by
  have h := checkLog_sound (w := (118631 / 881369)) (n := 12)
    (lo := (16927543 / 62500000)) (hi := (270840689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381369) = 1/(381369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-270840689 / 1000000000) (-16927543 / 62500000) (Real.log (381369 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53292091 / 250000000) ≤ -Real.log (1000000 / 1237593) ∧
    -Real.log (1000000 / 1237593) ≤ (42633673 / 200000000) := by
  have h := checkLog_sound (w := (237593 / 2237593)) (n := 12)
    (lo := (53292091 / 250000000)) (hi := (42633673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237593 / 1000000) = 1/(1000000 / 1237593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53292091 / 250000000) (42633673 / 200000000) (Real.log (1237593 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1237593 / 1000000) = -Real.log (1000000 / 1237593) := by
    rw [show ((1237593 / 1000000) : ℝ) = ((1000000 / 1237593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (54254949 / 200000000) ≤ -Real.log (762407 / 1000000) ∧
    -Real.log (762407 / 1000000) ≤ (135637373 / 500000000) := by
  have h := checkLog_sound (w := (237593 / 1762407)) (n := 12)
    (lo := (54254949 / 200000000)) (hi := (135637373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762407) = 1/(762407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-135637373 / 500000000) (-54254949 / 200000000) (Real.log (762407 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (675993937 / 1000000000) ≤ -Real.log (62500000000 / 122874129483) ∧
    -Real.log (62500000000 / 122874129483) ≤ (337996969 / 500000000) := by
  have h := checkLog_sound (w := (60374129483 / 185374129483)) (n := 12)
    (lo := (675993937 / 1000000000)) (hi := (337996969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122874129483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122874129483 / 62500000000) = 1/(62500000000 / 122874129483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (675993937 / 1000000000) (337996969 / 500000000) (Real.log (122874129483 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (122874129483 / 62500000000) = -Real.log (62500000000 / 122874129483) := by
    rw [show ((122874129483 / 62500000000) : ℝ) = ((62500000000 / 122874129483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (338475829 / 500000000) ≤ -Real.log (500000000000 / 983934920551) ∧
    -Real.log (500000000000 / 983934920551) ≤ (676951659 / 1000000000) := by
  have h := checkLog_sound (w := (483934920551 / 1483934920551)) (n := 12)
    (lo := (338475829 / 500000000)) (hi := (676951659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983934920551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983934920551 / 500000000000) = 1/(500000000000 / 983934920551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (338475829 / 500000000) (676951659 / 1000000000) (Real.log (983934920551 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (983934920551 / 500000000000) = -Real.log (500000000000 / 983934920551) := by
    rw [show ((983934920551 / 500000000000) : ℝ) = ((500000000000 / 983934920551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (483741561 / 1000000000) ≤ -Real.log (500000000000 / 811066185243) ∧
    -Real.log (500000000000 / 811066185243) ≤ (241870781 / 500000000) := by
  have h := checkLog_sound (w := (311066185243 / 1311066185243)) (n := 12)
    (lo := (483741561 / 1000000000)) (hi := (241870781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811066185243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811066185243 / 500000000000) = 1/(500000000000 / 811066185243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (483741561 / 1000000000) (241870781 / 500000000) (Real.log (811066185243 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (811066185243 / 500000000000) = -Real.log (500000000000 / 811066185243) := by
    rw [show ((811066185243 / 500000000000) : ℝ) = ((500000000000 / 811066185243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (484443109 / 1000000000) ≤ -Real.log (500000000000 / 811635386349) ∧
    -Real.log (500000000000 / 811635386349) ≤ (48444311 / 100000000) := by
  have h := checkLog_sound (w := (311635386349 / 1311635386349)) (n := 12)
    (lo := (484443109 / 1000000000)) (hi := (48444311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811635386349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811635386349 / 500000000000) = 1/(500000000000 / 811635386349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (484443109 / 1000000000) (48444311 / 100000000) (Real.log (811635386349 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (811635386349 / 500000000000) = -Real.log (500000000000 / 811635386349) := by
    rw [show ((811635386349 / 500000000000) : ℝ) = ((500000000000 / 811635386349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0377

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0378Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0378
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

theorem reflection_log_1_neg : (25686077 / 125000000) ≤ -Real.log (320 / 393) ∧
    -Real.log (320 / 393) ≤ (205488617 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 713)) (n := 12)
    (lo := (25686077 / 125000000)) (hi := (205488617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 320) = 1/(320 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25686077 / 125000000) (205488617 / 1000000000) (Real.log (393 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (393 / 320) = -Real.log (320 / 393) := by
    rw [show ((393 / 320) : ℝ) = ((320 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (258932659 / 1000000000) ≤ -Real.log (247 / 320) ∧
    -Real.log (247 / 320) ≤ (12946633 / 50000000) := by
  have h := checkLog_sound (w := (73 / 567)) (n := 12)
    (lo := (258932659 / 1000000000)) (hi := (12946633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 247) = 1/(247 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12946633 / 50000000) (-258932659 / 1000000000) (Real.log (247 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (205250037 / 1000000000) ≤ -Real.log (10240 / 12573) ∧
    -Real.log (10240 / 12573) ≤ (102625019 / 500000000) := by
  have h := checkLog_sound (w := (2333 / 22813)) (n := 12)
    (lo := (205250037 / 1000000000)) (hi := (102625019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12573 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12573 / 10240) = 1/(10240 / 12573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (205250037 / 1000000000) (102625019 / 500000000) (Real.log (12573 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12573 / 10240) = -Real.log (10240 / 12573) := by
    rw [show ((12573 / 10240) : ℝ) = ((10240 / 12573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32319147 / 125000000) ≤ -Real.log (7907 / 10240) ∧
    -Real.log (7907 / 10240) ≤ (258553177 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 18147)) (n := 12)
    (lo := (32319147 / 125000000)) (hi := (258553177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7907) = 1/(7907 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-258553177 / 1000000000) (-32319147 / 125000000) (Real.log (7907 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (187932319 / 500000000) ≤ -Real.log (160 / 233) ∧
    -Real.log (160 / 233) ≤ (375864639 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 393)) (n := 12)
    (lo := (187932319 / 500000000)) (hi := (375864639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233 / 160) = 1/(160 / 233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (187932319 / 500000000) (375864639 / 1000000000) (Real.log (233 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (233 / 160) = -Real.log (160 / 233) := by
    rw [show ((233 / 160) : ℝ) = ((160 / 233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (19039553 / 31250000) ≤ -Real.log (87 / 160) ∧
    -Real.log (87 / 160) ≤ (609265697 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 87) = 1/(87 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-609265697 / 1000000000) (-19039553 / 31250000) (Real.log (87 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93865549 / 250000000) ≤ -Real.log (5120 / 7453) ∧
    -Real.log (5120 / 7453) ≤ (375462197 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 12573)) (n := 12)
    (lo := (93865549 / 250000000)) (hi := (375462197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7453 / 5120) = 1/(5120 / 7453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93865549 / 250000000) (375462197 / 1000000000) (Real.log (7453 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7453 / 5120) = -Real.log (5120 / 7453) := by
    rw [show ((7453 / 5120) : ℝ) = ((5120 / 7453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60818869 / 100000000) ≤ -Real.log (2787 / 5120) ∧
    -Real.log (2787 / 5120) ≤ (608188691 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 7907)) (n := 12)
    (lo := (60818869 / 100000000)) (hi := (608188691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2787) = 1/(2787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-608188691 / 1000000000) (-60818869 / 100000000) (Real.log (2787 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (281609421 / 1000000000) ≤ -Real.log (1000000 / 1325261) ∧
    -Real.log (1000000 / 1325261) ≤ (140804711 / 500000000) := by
  have h := checkLog_sound (w := (325261 / 2325261)) (n := 12)
    (lo := (281609421 / 1000000000)) (hi := (140804711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325261 / 1000000) = 1/(1000000 / 1325261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (281609421 / 1000000000) (140804711 / 500000000) (Real.log (1325261 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1325261 / 1000000) = -Real.log (1000000 / 1325261) := by
    rw [show ((1325261 / 1000000) : ℝ) = ((1000000 / 1325261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (393429329 / 1000000000) ≤ -Real.log (674739 / 1000000) ∧
    -Real.log (674739 / 1000000) ≤ (39342933 / 100000000) := by
  have h := checkLog_sound (w := (325261 / 1674739)) (n := 12)
    (lo := (393429329 / 1000000000)) (hi := (39342933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674739) = 1/(674739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-39342933 / 100000000) (-393429329 / 1000000000) (Real.log (674739 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (70483081 / 250000000) ≤ -Real.log (1000000 / 1325689) ∧
    -Real.log (1000000 / 1325689) ≤ (11277293 / 40000000) := by
  have h := checkLog_sound (w := (325689 / 2325689)) (n := 12)
    (lo := (70483081 / 250000000)) (hi := (11277293 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325689 / 1000000) = 1/(1000000 / 1325689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (70483081 / 250000000) (11277293 / 40000000) (Real.log (1325689 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1325689 / 1000000) = -Real.log (1000000 / 1325689) := by
    rw [show ((1325689 / 1000000) : ℝ) = ((1000000 / 1325689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7881277 / 20000000) ≤ -Real.log (674311 / 1000000) ∧
    -Real.log (674311 / 1000000) ≤ (394063851 / 1000000000) := by
  have h := checkLog_sound (w := (325689 / 1674311)) (n := 12)
    (lo := (7881277 / 20000000)) (hi := (394063851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674311) = 1/(674311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-394063851 / 1000000000) (-7881277 / 20000000) (Real.log (674311 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5315853 / 25000000) ≤ -Real.log (250000 / 309233) ∧
    -Real.log (250000 / 309233) ≤ (212634121 / 1000000000) := by
  have h := checkLog_sound (w := (59233 / 559233)) (n := 12)
    (lo := (5315853 / 25000000)) (hi := (212634121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309233 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309233 / 250000) = 1/(250000 / 309233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5315853 / 25000000) (212634121 / 1000000000) (Real.log (309233 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (309233 / 250000) = -Real.log (250000 / 309233) := by
    rw [show ((309233 / 250000) : ℝ) = ((250000 / 309233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (270408129 / 1000000000) ≤ -Real.log (190767 / 250000) ∧
    -Real.log (190767 / 250000) ≤ (27040813 / 100000000) := by
  have h := checkLog_sound (w := (59233 / 440767)) (n := 12)
    (lo := (270408129 / 1000000000)) (hi := (27040813 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190767) = 1/(190767 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-27040813 / 100000000) (-270408129 / 1000000000) (Real.log (190767 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (212901681 / 1000000000) ≤ -Real.log (1000000 / 1237263) ∧
    -Real.log (1000000 / 1237263) ≤ (106450841 / 500000000) := by
  have h := checkLog_sound (w := (237263 / 2237263)) (n := 12)
    (lo := (212901681 / 1000000000)) (hi := (106450841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237263 / 1000000) = 1/(1000000 / 1237263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (212901681 / 1000000000) (106450841 / 500000000) (Real.log (1237263 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1237263 / 1000000) = -Real.log (1000000 / 1237263) := by
    rw [show ((1237263 / 1000000) : ℝ) = ((1000000 / 1237263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (270841999 / 1000000000) ≤ -Real.log (762737 / 1000000) ∧
    -Real.log (762737 / 1000000) ≤ (135421 / 500000) := by
  have h := checkLog_sound (w := (237263 / 1762737)) (n := 12)
    (lo := (270841999 / 1000000000)) (hi := (135421 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762737) = 1/(762737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-135421 / 500000) (-270841999 / 1000000000) (Real.log (762737 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (540031 / 800000) ≤ -Real.log (500000000000 / 982054542571) ∧
    -Real.log (500000000000 / 982054542571) ≤ (675038751 / 1000000000) := by
  have h := checkLog_sound (w := (482054542571 / 1482054542571)) (n := 12)
    (lo := (540031 / 800000)) (hi := (675038751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982054542571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982054542571 / 500000000000) = 1/(500000000000 / 982054542571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (540031 / 800000) (675038751 / 1000000000) (Real.log (982054542571 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (982054542571 / 500000000000) = -Real.log (500000000000 / 982054542571) := by
    rw [show ((982054542571 / 500000000000) : ℝ) = ((500000000000 / 982054542571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (337998087 / 500000000) ≤ -Real.log (500000000000 / 982995235137) ∧
    -Real.log (500000000000 / 982995235137) ≤ (27039847 / 40000000) := by
  have h := checkLog_sound (w := (482995235137 / 1482995235137)) (n := 12)
    (lo := (337998087 / 500000000)) (hi := (27039847 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982995235137 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982995235137 / 500000000000) = 1/(500000000000 / 982995235137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (337998087 / 500000000) (27039847 / 40000000) (Real.log (982995235137 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (982995235137 / 500000000000) = -Real.log (500000000000 / 982995235137) := by
    rw [show ((982995235137 / 500000000000) : ℝ) = ((500000000000 / 982995235137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (483042249 / 1000000000) ≤ -Real.log (500000000000 / 810499195353) ∧
    -Real.log (500000000000 / 810499195353) ≤ (1932169 / 4000000) := by
  have h := checkLog_sound (w := (310499195353 / 1310499195353)) (n := 12)
    (lo := (483042249 / 1000000000)) (hi := (1932169 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((810499195353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(810499195353 / 500000000000) = 1/(500000000000 / 810499195353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (483042249 / 1000000000) (1932169 / 4000000) (Real.log (810499195353 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (810499195353 / 500000000000) = -Real.log (500000000000 / 810499195353) := by
    rw [show ((810499195353 / 500000000000) : ℝ) = ((500000000000 / 810499195353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (483743681 / 1000000000) ≤ -Real.log (25000000000 / 40553395207) ∧
    -Real.log (25000000000 / 40553395207) ≤ (241871841 / 500000000) := by
  have h := checkLog_sound (w := (15553395207 / 65553395207)) (n := 12)
    (lo := (483743681 / 1000000000)) (hi := (241871841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40553395207 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40553395207 / 25000000000) = 1/(25000000000 / 40553395207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (483743681 / 1000000000) (241871841 / 500000000) (Real.log (40553395207 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (40553395207 / 25000000000) = -Real.log (25000000000 / 40553395207) := by
    rw [show ((40553395207 / 25000000000) : ℝ) = ((25000000000 / 40553395207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0378

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0379Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0379
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

theorem reflection_log_1_neg : (205250037 / 1000000000) ≤ -Real.log (10240 / 12573) ∧
    -Real.log (10240 / 12573) ≤ (102625019 / 500000000) := by
  have h := checkLog_sound (w := (2333 / 22813)) (n := 12)
    (lo := (205250037 / 1000000000)) (hi := (102625019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12573 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12573 / 10240) = 1/(10240 / 12573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (205250037 / 1000000000) (102625019 / 500000000) (Real.log (12573 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12573 / 10240) = -Real.log (10240 / 12573) := by
    rw [show ((12573 / 10240) : ℝ) = ((10240 / 12573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32319147 / 125000000) ≤ -Real.log (7907 / 10240) ∧
    -Real.log (7907 / 10240) ≤ (258553177 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 18147)) (n := 12)
    (lo := (32319147 / 125000000)) (hi := (258553177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7907) = 1/(7907 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-258553177 / 1000000000) (-32319147 / 125000000) (Real.log (7907 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (102505701 / 500000000) ≤ -Real.log (1024 / 1257) ∧
    -Real.log (1024 / 1257) ≤ (205011403 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2281)) (n := 12)
    (lo := (102505701 / 500000000)) (hi := (205011403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257 / 1024) = 1/(1024 / 1257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (102505701 / 500000000) (205011403 / 1000000000) (Real.log (1257 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1257 / 1024) = -Real.log (1024 / 1257) := by
    rw [show ((1257 / 1024) : ℝ) = ((1024 / 1257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (258173837 / 1000000000) ≤ -Real.log (791 / 1024) ∧
    -Real.log (791 / 1024) ≤ (129086919 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1815)) (n := 12)
    (lo := (258173837 / 1000000000)) (hi := (129086919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 791) = 1/(791 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-129086919 / 500000000) (-258173837 / 1000000000) (Real.log (791 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93865549 / 250000000) ≤ -Real.log (5120 / 7453) ∧
    -Real.log (5120 / 7453) ≤ (375462197 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 12573)) (n := 12)
    (lo := (93865549 / 250000000)) (hi := (375462197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7453 / 5120) = 1/(5120 / 7453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93865549 / 250000000) (375462197 / 1000000000) (Real.log (7453 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7453 / 5120) = -Real.log (5120 / 7453) := by
    rw [show ((7453 / 5120) : ℝ) = ((5120 / 7453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (60818869 / 100000000) ≤ -Real.log (2787 / 5120) ∧
    -Real.log (2787 / 5120) ≤ (608188691 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 7907)) (n := 12)
    (lo := (60818869 / 100000000)) (hi := (608188691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2787) = 1/(2787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-608188691 / 1000000000) (-60818869 / 100000000) (Real.log (2787 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (375059593 / 1000000000) ≤ -Real.log (512 / 745) ∧
    -Real.log (512 / 745) ≤ (187529797 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1257)) (n := 12)
    (lo := (375059593 / 1000000000)) (hi := (187529797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745 / 512) = 1/(512 / 745) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (375059593 / 1000000000) (187529797 / 500000000) (Real.log (745 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (745 / 512) = -Real.log (512 / 745) := by
    rw [show ((745 / 512) : ℝ) = ((512 / 745) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (607112843 / 1000000000) ≤ -Real.log (279 / 512) ∧
    -Real.log (279 / 512) ≤ (151778211 / 250000000) := by
  have h := checkLog_sound (w := (233 / 791)) (n := 12)
    (lo := (607112843 / 1000000000)) (hi := (151778211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 279) = 1/(279 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-151778211 / 250000000) (-607112843 / 1000000000) (Real.log (279 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (549389 / 1953125) ≤ -Real.log (500000 / 662417) ∧
    -Real.log (500000 / 662417) ≤ (281287169 / 1000000000) := by
  have h := checkLog_sound (w := (162417 / 1162417)) (n := 12)
    (lo := (549389 / 1953125)) (hi := (281287169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662417 / 500000) = 1/(500000 / 662417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (549389 / 1953125) (281287169 / 1000000000) (Real.log (662417 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (662417 / 500000) = -Real.log (500000 / 662417) := by
    rw [show ((662417 / 500000) : ℝ) = ((500000 / 662417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (98199173 / 250000000) ≤ -Real.log (337583 / 500000) ∧
    -Real.log (337583 / 500000) ≤ (392796693 / 1000000000) := by
  have h := checkLog_sound (w := (162417 / 837583)) (n := 12)
    (lo := (98199173 / 250000000)) (hi := (392796693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 337583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 337583) = 1/(337583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-392796693 / 1000000000) (-98199173 / 250000000) (Real.log (337583 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11264407 / 40000000) ≤ -Real.log (500000 / 662631) ∧
    -Real.log (500000 / 662631) ≤ (4400159 / 15625000) := by
  have h := checkLog_sound (w := (162631 / 1162631)) (n := 12)
    (lo := (11264407 / 40000000)) (hi := (4400159 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662631 / 500000) = 1/(500000 / 662631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11264407 / 40000000) (4400159 / 15625000) (Real.log (662631 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (662631 / 500000) = -Real.log (500000 / 662631) := by
    rw [show ((662631 / 500000) : ℝ) = ((500000 / 662631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (393430811 / 1000000000) ≤ -Real.log (337369 / 500000) ∧
    -Real.log (337369 / 500000) ≤ (98357703 / 250000000) := by
  have h := checkLog_sound (w := (162631 / 837369)) (n := 12)
    (lo := (393430811 / 1000000000)) (hi := (98357703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 337369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 337369) = 1/(337369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-98357703 / 250000000) (-393430811 / 1000000000) (Real.log (337369 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42473459 / 200000000) ≤ -Real.log (500000 / 618301) ∧
    -Real.log (500000 / 618301) ≤ (3318239 / 15625000) := by
  have h := checkLog_sound (w := (118301 / 1118301)) (n := 12)
    (lo := (42473459 / 200000000)) (hi := (3318239 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618301 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618301 / 500000) = 1/(500000 / 618301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42473459 / 200000000) (3318239 / 15625000) (Real.log (618301 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (618301 / 500000) = -Real.log (500000 / 618301) := by
    rw [show ((618301 / 500000) : ℝ) = ((500000 / 618301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (134987879 / 500000000) ≤ -Real.log (381699 / 500000) ∧
    -Real.log (381699 / 500000) ≤ (269975759 / 1000000000) := by
  have h := checkLog_sound (w := (118301 / 881699)) (n := 12)
    (lo := (134987879 / 500000000)) (hi := (269975759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381699) = 1/(381699 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-269975759 / 1000000000) (-134987879 / 500000000) (Real.log (381699 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (13289683 / 62500000) ≤ -Real.log (1000000 / 1236933) ∧
    -Real.log (1000000 / 1236933) ≤ (212634929 / 1000000000) := by
  have h := checkLog_sound (w := (236933 / 2236933)) (n := 12)
    (lo := (13289683 / 62500000)) (hi := (212634929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236933 / 1000000) = 1/(1000000 / 1236933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (13289683 / 62500000) (212634929 / 1000000000) (Real.log (1236933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1236933 / 1000000) = -Real.log (1000000 / 1236933) := by
    rw [show ((1236933 / 1000000) : ℝ) = ((1000000 / 1236933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1690059 / 6250000) ≤ -Real.log (763067 / 1000000) ∧
    -Real.log (763067 / 1000000) ≤ (270409441 / 1000000000) := by
  have h := checkLog_sound (w := (236933 / 1763067)) (n := 12)
    (lo := (1690059 / 6250000)) (hi := (270409441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763067) = 1/(763067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-270409441 / 1000000000) (-1690059 / 6250000) (Real.log (763067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (33704193 / 50000000) ≤ -Real.log (500000000000 / 981117236353) ∧
    -Real.log (500000000000 / 981117236353) ≤ (674083861 / 1000000000) := by
  have h := checkLog_sound (w := (481117236353 / 1481117236353)) (n := 12)
    (lo := (33704193 / 50000000)) (hi := (674083861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981117236353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981117236353 / 500000000000) = 1/(500000000000 / 981117236353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33704193 / 50000000) (674083861 / 1000000000) (Real.log (981117236353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (981117236353 / 500000000000) = -Real.log (500000000000 / 981117236353) := by
    rw [show ((981117236353 / 500000000000) : ℝ) = ((500000000000 / 981117236353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (675040987 / 1000000000) ≤ -Real.log (500000000000 / 982056739061) ∧
    -Real.log (500000000000 / 982056739061) ≤ (168760247 / 250000000) := by
  have h := checkLog_sound (w := (482056739061 / 1482056739061)) (n := 12)
    (lo := (675040987 / 1000000000)) (hi := (168760247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982056739061 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982056739061 / 500000000000) = 1/(500000000000 / 982056739061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (675040987 / 1000000000) (168760247 / 250000000) (Real.log (982056739061 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (982056739061 / 500000000000) = -Real.log (500000000000 / 982056739061) := by
    rw [show ((982056739061 / 500000000000) : ℝ) = ((500000000000 / 982056739061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (241171527 / 500000000) ≤ -Real.log (250000000000 / 404966347829) ∧
    -Real.log (250000000000 / 404966347829) ≤ (96468611 / 200000000) := by
  have h := checkLog_sound (w := (154966347829 / 654966347829)) (n := 12)
    (lo := (241171527 / 500000000)) (hi := (96468611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404966347829 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404966347829 / 250000000000) = 1/(250000000000 / 404966347829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (241171527 / 500000000) (96468611 / 200000000) (Real.log (404966347829 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (404966347829 / 250000000000) = -Real.log (250000000000 / 404966347829) := by
    rw [show ((404966347829 / 250000000000) : ℝ) = ((250000000000 / 404966347829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (30190273 / 62500000) ≤ -Real.log (125000000000 / 202625228191) ∧
    -Real.log (125000000000 / 202625228191) ≤ (483044369 / 1000000000) := by
  have h := checkLog_sound (w := (77625228191 / 327625228191)) (n := 12)
    (lo := (30190273 / 62500000)) (hi := (483044369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202625228191 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202625228191 / 125000000000) = 1/(125000000000 / 202625228191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (30190273 / 62500000) (483044369 / 1000000000) (Real.log (202625228191 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (202625228191 / 125000000000) = -Real.log (125000000000 / 202625228191) := by
    rw [show ((202625228191 / 125000000000) : ℝ) = ((125000000000 / 202625228191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0379

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0380Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0380
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

theorem reflection_log_1_neg : (102505701 / 500000000) ≤ -Real.log (1024 / 1257) ∧
    -Real.log (1024 / 1257) ≤ (205011403 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2281)) (n := 12)
    (lo := (102505701 / 500000000)) (hi := (205011403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257 / 1024) = 1/(1024 / 1257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (102505701 / 500000000) (205011403 / 1000000000) (Real.log (1257 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1257 / 1024) = -Real.log (1024 / 1257) := by
    rw [show ((1257 / 1024) : ℝ) = ((1024 / 1257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (258173837 / 1000000000) ≤ -Real.log (791 / 1024) ∧
    -Real.log (791 / 1024) ≤ (129086919 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1815)) (n := 12)
    (lo := (258173837 / 1000000000)) (hi := (129086919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 791) = 1/(791 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-129086919 / 500000000) (-258173837 / 1000000000) (Real.log (791 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (204772711 / 1000000000) ≤ -Real.log (10240 / 12567) ∧
    -Real.log (10240 / 12567) ≤ (25596589 / 125000000) := by
  have h := checkLog_sound (w := (2327 / 22807)) (n := 12)
    (lo := (204772711 / 1000000000)) (hi := (25596589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12567 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12567 / 10240) = 1/(10240 / 12567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (204772711 / 1000000000) (25596589 / 125000000) (Real.log (12567 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12567 / 10240) = -Real.log (10240 / 12567) := by
    rw [show ((12567 / 10240) : ℝ) = ((10240 / 12567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (128897321 / 500000000) ≤ -Real.log (7913 / 10240) ∧
    -Real.log (7913 / 10240) ≤ (257794643 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 18153)) (n := 12)
    (lo := (128897321 / 500000000)) (hi := (257794643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7913) = 1/(7913 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-257794643 / 1000000000) (-128897321 / 500000000) (Real.log (7913 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (375059593 / 1000000000) ≤ -Real.log (512 / 745) ∧
    -Real.log (512 / 745) ≤ (187529797 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1257)) (n := 12)
    (lo := (375059593 / 1000000000)) (hi := (187529797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745 / 512) = 1/(512 / 745) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (375059593 / 1000000000) (187529797 / 500000000) (Real.log (745 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (745 / 512) = -Real.log (512 / 745) := by
    rw [show ((745 / 512) : ℝ) = ((512 / 745) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (607112843 / 1000000000) ≤ -Real.log (279 / 512) ∧
    -Real.log (279 / 512) ≤ (151778211 / 250000000) := by
  have h := checkLog_sound (w := (233 / 791)) (n := 12)
    (lo := (607112843 / 1000000000)) (hi := (151778211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 279) = 1/(279 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-151778211 / 250000000) (-607112843 / 1000000000) (Real.log (279 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (374656827 / 1000000000) ≤ -Real.log (5120 / 7447) ∧
    -Real.log (5120 / 7447) ≤ (93664207 / 250000000) := by
  have h := checkLog_sound (w := (2327 / 12567)) (n := 12)
    (lo := (374656827 / 1000000000)) (hi := (93664207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7447 / 5120) = 1/(5120 / 7447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (374656827 / 1000000000) (93664207 / 250000000) (Real.log (7447 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7447 / 5120) = -Real.log (5120 / 7447) := by
    rw [show ((7447 / 5120) : ℝ) = ((5120 / 7447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75754769 / 125000000) ≤ -Real.log (2793 / 5120) ∧
    -Real.log (2793 / 5120) ≤ (606038153 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 7913)) (n := 12)
    (lo := (75754769 / 125000000)) (hi := (606038153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2793) = 1/(2793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-606038153 / 1000000000) (-75754769 / 125000000) (Real.log (2793 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (70241203 / 250000000) ≤ -Real.log (1000000 / 1324407) ∧
    -Real.log (1000000 / 1324407) ≤ (280964813 / 1000000000) := by
  have h := checkLog_sound (w := (324407 / 2324407)) (n := 12)
    (lo := (70241203 / 250000000)) (hi := (280964813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1324407 / 1000000) = 1/(1000000 / 1324407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (70241203 / 250000000) (280964813 / 1000000000) (Real.log (1324407 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1324407 / 1000000) = -Real.log (1000000 / 1324407) := by
    rw [show ((1324407 / 1000000) : ℝ) = ((1000000 / 1324407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (78432891 / 200000000) ≤ -Real.log (675593 / 1000000) ∧
    -Real.log (675593 / 1000000) ≤ (49020557 / 125000000) := by
  have h := checkLog_sound (w := (324407 / 1675593)) (n := 12)
    (lo := (78432891 / 200000000)) (hi := (49020557 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 675593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 675593) = 1/(675593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49020557 / 125000000) (-78432891 / 200000000) (Real.log (675593 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (281287923 / 1000000000) ≤ -Real.log (200000 / 264967) ∧
    -Real.log (200000 / 264967) ≤ (70321981 / 250000000) := by
  have h := checkLog_sound (w := (64967 / 464967)) (n := 12)
    (lo := (281287923 / 1000000000)) (hi := (70321981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264967 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(264967 / 200000) = 1/(200000 / 264967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (281287923 / 1000000000) (70321981 / 250000000) (Real.log (264967 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (264967 / 200000) = -Real.log (200000 / 264967) := by
    rw [show ((264967 / 200000) : ℝ) = ((200000 / 264967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (392798173 / 1000000000) ≤ -Real.log (135033 / 200000) ∧
    -Real.log (135033 / 200000) ≤ (196399087 / 500000000) := by
  have h := checkLog_sound (w := (64967 / 335033)) (n := 12)
    (lo := (392798173 / 1000000000)) (hi := (196399087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 135033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 135033) = 1/(135033 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-196399087 / 500000000) (-392798173 / 1000000000) (Real.log (135033 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26512651 / 125000000) ≤ -Real.log (1000000 / 1236273) ∧
    -Real.log (1000000 / 1236273) ≤ (212101209 / 1000000000) := by
  have h := checkLog_sound (w := (236273 / 2236273)) (n := 12)
    (lo := (26512651 / 125000000)) (hi := (212101209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236273 / 1000000) = 1/(1000000 / 1236273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26512651 / 125000000) (212101209 / 1000000000) (Real.log (1236273 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1236273 / 1000000) = -Real.log (1000000 / 1236273) := by
    rw [show ((1236273 / 1000000) : ℝ) = ((1000000 / 1236273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (269544883 / 1000000000) ≤ -Real.log (763727 / 1000000) ∧
    -Real.log (763727 / 1000000) ≤ (67386221 / 250000000) := by
  have h := checkLog_sound (w := (236273 / 1763727)) (n := 12)
    (lo := (269544883 / 1000000000)) (hi := (67386221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763727) = 1/(763727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-67386221 / 250000000) (-269544883 / 1000000000) (Real.log (763727 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (26546013 / 125000000) ≤ -Real.log (1000000 / 1236603) ∧
    -Real.log (1000000 / 1236603) ≤ (42473621 / 200000000) := by
  have h := checkLog_sound (w := (236603 / 2236603)) (n := 12)
    (lo := (26546013 / 125000000)) (hi := (42473621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236603 / 1000000) = 1/(1000000 / 1236603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (26546013 / 125000000) (42473621 / 200000000) (Real.log (1236603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1236603 / 1000000) = -Real.log (1000000 / 1236603) := by
    rw [show ((1236603 / 1000000) : ℝ) = ((1000000 / 1236603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (67494267 / 250000000) ≤ -Real.log (763397 / 1000000) ∧
    -Real.log (763397 / 1000000) ≤ (269977069 / 1000000000) := by
  have h := checkLog_sound (w := (236603 / 1763397)) (n := 12)
    (lo := (67494267 / 250000000)) (hi := (269977069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763397) = 1/(763397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-269977069 / 1000000000) (-67494267 / 250000000) (Real.log (763397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (673129267 / 1000000000) ≤ -Real.log (500000000000 / 980181114961) ∧
    -Real.log (500000000000 / 980181114961) ≤ (168282317 / 250000000) := by
  have h := checkLog_sound (w := (480181114961 / 1480181114961)) (n := 12)
    (lo := (673129267 / 1000000000)) (hi := (168282317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980181114961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980181114961 / 500000000000) = 1/(500000000000 / 980181114961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (673129267 / 1000000000) (168282317 / 250000000) (Real.log (980181114961 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (980181114961 / 500000000000) = -Real.log (500000000000 / 980181114961) := by
    rw [show ((980181114961 / 500000000000) : ℝ) = ((500000000000 / 980181114961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (42130381 / 62500000) ≤ -Real.log (250000000000 / 490559715033) ∧
    -Real.log (250000000000 / 490559715033) ≤ (674086097 / 1000000000) := by
  have h := checkLog_sound (w := (240559715033 / 740559715033)) (n := 12)
    (lo := (42130381 / 62500000)) (hi := (674086097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490559715033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490559715033 / 250000000000) = 1/(250000000000 / 490559715033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (42130381 / 62500000) (674086097 / 1000000000) (Real.log (490559715033 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (490559715033 / 250000000000) = -Real.log (250000000000 / 490559715033) := by
    rw [show ((490559715033 / 250000000000) : ℝ) = ((250000000000 / 490559715033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (481646091 / 1000000000) ≤ -Real.log (125000000000 / 202342099991) ∧
    -Real.log (125000000000 / 202342099991) ≤ (120411523 / 250000000) := by
  have h := checkLog_sound (w := (77342099991 / 327342099991)) (n := 12)
    (lo := (481646091 / 1000000000)) (hi := (120411523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202342099991 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202342099991 / 125000000000) = 1/(125000000000 / 202342099991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (481646091 / 1000000000) (120411523 / 250000000) (Real.log (202342099991 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (202342099991 / 125000000000) = -Real.log (125000000000 / 202342099991) := by
    rw [show ((202342099991 / 125000000000) : ℝ) = ((125000000000 / 202342099991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (120586293 / 250000000) ≤ -Real.log (100000000000 / 161986882317) ∧
    -Real.log (100000000000 / 161986882317) ≤ (482345173 / 1000000000) := by
  have h := checkLog_sound (w := (61986882317 / 261986882317)) (n := 12)
    (lo := (120586293 / 250000000)) (hi := (482345173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161986882317 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161986882317 / 100000000000) = 1/(100000000000 / 161986882317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (120586293 / 250000000) (482345173 / 1000000000) (Real.log (161986882317 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (161986882317 / 100000000000) = -Real.log (100000000000 / 161986882317) := by
    rw [show ((161986882317 / 100000000000) : ℝ) = ((100000000000 / 161986882317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0380

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0381Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0381
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

theorem reflection_log_1_neg : (204772711 / 1000000000) ≤ -Real.log (10240 / 12567) ∧
    -Real.log (10240 / 12567) ≤ (25596589 / 125000000) := by
  have h := checkLog_sound (w := (2327 / 22807)) (n := 12)
    (lo := (204772711 / 1000000000)) (hi := (25596589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12567 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12567 / 10240) = 1/(10240 / 12567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (204772711 / 1000000000) (25596589 / 125000000) (Real.log (12567 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12567 / 10240) = -Real.log (10240 / 12567) := by
    rw [show ((12567 / 10240) : ℝ) = ((10240 / 12567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (128897321 / 500000000) ≤ -Real.log (7913 / 10240) ∧
    -Real.log (7913 / 10240) ≤ (257794643 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 18153)) (n := 12)
    (lo := (128897321 / 500000000)) (hi := (257794643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7913) = 1/(7913 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-257794643 / 1000000000) (-128897321 / 500000000) (Real.log (7913 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (102266981 / 500000000) ≤ -Real.log (2560 / 3141) ∧
    -Real.log (2560 / 3141) ≤ (204533963 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 5701)) (n := 12)
    (lo := (102266981 / 500000000)) (hi := (204533963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3141 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3141 / 2560) = 1/(2560 / 3141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (102266981 / 500000000) (204533963 / 1000000000) (Real.log (3141 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3141 / 2560) = -Real.log (2560 / 3141) := by
    rw [show ((3141 / 2560) : ℝ) = ((2560 / 3141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (257415591 / 1000000000) ≤ -Real.log (1979 / 2560) ∧
    -Real.log (1979 / 2560) ≤ (32176949 / 125000000) := by
  have h := checkLog_sound (w := (581 / 4539)) (n := 12)
    (lo := (257415591 / 1000000000)) (hi := (32176949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1979) = 1/(1979 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-32176949 / 125000000) (-257415591 / 1000000000) (Real.log (1979 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (374656827 / 1000000000) ≤ -Real.log (5120 / 7447) ∧
    -Real.log (5120 / 7447) ≤ (93664207 / 250000000) := by
  have h := checkLog_sound (w := (2327 / 12567)) (n := 12)
    (lo := (374656827 / 1000000000)) (hi := (93664207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7447 / 5120) = 1/(5120 / 7447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (374656827 / 1000000000) (93664207 / 250000000) (Real.log (7447 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7447 / 5120) = -Real.log (5120 / 7447) := by
    rw [show ((7447 / 5120) : ℝ) = ((5120 / 7447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (75754769 / 125000000) ≤ -Real.log (2793 / 5120) ∧
    -Real.log (2793 / 5120) ≤ (606038153 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 7913)) (n := 12)
    (lo := (75754769 / 125000000)) (hi := (606038153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2793) = 1/(2793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-606038153 / 1000000000) (-75754769 / 125000000) (Real.log (2793 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (374253899 / 1000000000) ≤ -Real.log (1280 / 1861) ∧
    -Real.log (1280 / 1861) ≤ (3742539 / 10000000) := by
  have h := checkLog_sound (w := (581 / 3141)) (n := 12)
    (lo := (374253899 / 1000000000)) (hi := (3742539 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1861 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1861 / 1280) = 1/(1280 / 1861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (374253899 / 1000000000) (3742539 / 10000000) (Real.log (1861 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1861 / 1280) = -Real.log (1280 / 1861) := by
    rw [show ((1861 / 1280) : ℝ) = ((1280 / 1861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (302482307 / 500000000) ≤ -Real.log (699 / 1280) ∧
    -Real.log (699 / 1280) ≤ (120992923 / 200000000) := by
  have h := checkLog_sound (w := (581 / 1979)) (n := 12)
    (lo := (302482307 / 500000000)) (hi := (120992923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 699) = 1/(699 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-120992923 / 200000000) (-302482307 / 500000000) (Real.log (699 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (280642351 / 1000000000) ≤ -Real.log (50000 / 66199) ∧
    -Real.log (50000 / 66199) ≤ (17540147 / 62500000) := by
  have h := checkLog_sound (w := (16199 / 116199)) (n := 12)
    (lo := (280642351 / 1000000000)) (hi := (17540147 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66199 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66199 / 50000) = 1/(50000 / 66199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (280642351 / 1000000000) (17540147 / 62500000) (Real.log (66199 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (66199 / 50000) = -Real.log (50000 / 66199) := by
    rw [show ((66199 / 50000) : ℝ) = ((50000 / 66199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (391532617 / 1000000000) ≤ -Real.log (33801 / 50000) ∧
    -Real.log (33801 / 50000) ≤ (195766309 / 500000000) := by
  have h := checkLog_sound (w := (16199 / 83801)) (n := 12)
    (lo := (391532617 / 1000000000)) (hi := (195766309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33801) = 1/(33801 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-195766309 / 500000000) (-391532617 / 1000000000) (Real.log (33801 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (280965567 / 1000000000) ≤ -Real.log (125000 / 165551) ∧
    -Real.log (125000 / 165551) ≤ (4390087 / 15625000) := by
  have h := checkLog_sound (w := (40551 / 290551)) (n := 12)
    (lo := (280965567 / 1000000000)) (hi := (4390087 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165551 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165551 / 125000) = 1/(125000 / 165551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (280965567 / 1000000000) (4390087 / 15625000) (Real.log (165551 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165551 / 125000) = -Real.log (125000 / 165551) := by
    rw [show ((165551 / 125000) : ℝ) = ((125000 / 165551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (78433187 / 200000000) ≤ -Real.log (84449 / 125000) ∧
    -Real.log (84449 / 125000) ≤ (24510371 / 62500000) := by
  have h := checkLog_sound (w := (40551 / 209449)) (n := 12)
    (lo := (78433187 / 200000000)) (hi := (24510371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84449) = 1/(84449 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24510371 / 62500000) (-78433187 / 200000000) (Real.log (84449 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (211834241 / 1000000000) ≤ -Real.log (1000000 / 1235943) ∧
    -Real.log (1000000 / 1235943) ≤ (105917121 / 500000000) := by
  have h := checkLog_sound (w := (235943 / 2235943)) (n := 12)
    (lo := (211834241 / 1000000000)) (hi := (105917121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235943 / 1000000) = 1/(1000000 / 1235943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (211834241 / 1000000000) (105917121 / 500000000) (Real.log (1235943 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1235943 / 1000000) = -Real.log (1000000 / 1235943) := by
    rw [show ((1235943 / 1000000) : ℝ) = ((1000000 / 1235943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (53822577 / 200000000) ≤ -Real.log (764057 / 1000000) ∧
    -Real.log (764057 / 1000000) ≤ (134556443 / 500000000) := by
  have h := checkLog_sound (w := (235943 / 1764057)) (n := 12)
    (lo := (53822577 / 200000000)) (hi := (134556443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764057) = 1/(764057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-134556443 / 500000000) (-53822577 / 200000000) (Real.log (764057 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (212102017 / 1000000000) ≤ -Real.log (500000 / 618137) ∧
    -Real.log (500000 / 618137) ≤ (106051009 / 500000000) := by
  have h := checkLog_sound (w := (118137 / 1118137)) (n := 12)
    (lo := (212102017 / 1000000000)) (hi := (106051009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618137 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618137 / 500000) = 1/(500000 / 618137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (212102017 / 1000000000) (106051009 / 500000000) (Real.log (618137 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (618137 / 500000) = -Real.log (500000 / 618137) := by
    rw [show ((618137 / 500000) : ℝ) = ((500000 / 618137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16846637 / 62500000) ≤ -Real.log (381863 / 500000) ∧
    -Real.log (381863 / 500000) ≤ (269546193 / 1000000000) := by
  have h := checkLog_sound (w := (118137 / 881863)) (n := 12)
    (lo := (16846637 / 62500000)) (hi := (269546193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381863) = 1/(381863 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-269546193 / 1000000000) (-16846637 / 62500000) (Real.log (381863 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (672174969 / 1000000000) ≤ -Real.log (125000000000 / 244811544037) ∧
    -Real.log (125000000000 / 244811544037) ≤ (67217497 / 100000000) := by
  have h := checkLog_sound (w := (119811544037 / 369811544037)) (n := 12)
    (lo := (672174969 / 1000000000)) (hi := (67217497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244811544037 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244811544037 / 125000000000) = 1/(125000000000 / 244811544037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (672174969 / 1000000000) (67217497 / 100000000) (Real.log (244811544037 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (244811544037 / 125000000000) = -Real.log (125000000000 / 244811544037) := by
    rw [show ((244811544037 / 125000000000) : ℝ) = ((125000000000 / 244811544037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (336565751 / 500000000) ≤ -Real.log (500000000000 / 980183305901) ∧
    -Real.log (500000000000 / 980183305901) ≤ (673131503 / 1000000000) := by
  have h := checkLog_sound (w := (480183305901 / 1480183305901)) (n := 12)
    (lo := (336565751 / 500000000)) (hi := (673131503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980183305901 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980183305901 / 500000000000) = 1/(500000000000 / 980183305901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (336565751 / 500000000) (673131503 / 1000000000) (Real.log (980183305901 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (980183305901 / 500000000000) = -Real.log (500000000000 / 980183305901) := by
    rw [show ((980183305901 / 500000000000) : ℝ) = ((500000000000 / 980183305901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (240473563 / 500000000) ≤ -Real.log (62500000000 / 101100359659) ∧
    -Real.log (62500000000 / 101100359659) ≤ (480947127 / 1000000000) := by
  have h := checkLog_sound (w := (38600359659 / 163600359659)) (n := 12)
    (lo := (240473563 / 500000000)) (hi := (480947127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101100359659 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101100359659 / 62500000000) = 1/(62500000000 / 101100359659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (240473563 / 500000000) (480947127 / 1000000000) (Real.log (101100359659 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (101100359659 / 62500000000) = -Real.log (62500000000 / 101100359659) := by
    rw [show ((101100359659 / 62500000000) : ℝ) = ((62500000000 / 101100359659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (48164821 / 100000000) ≤ -Real.log (500000000000 / 809370114413) ∧
    -Real.log (500000000000 / 809370114413) ≤ (481648211 / 1000000000) := by
  have h := checkLog_sound (w := (309370114413 / 1309370114413)) (n := 12)
    (lo := (48164821 / 100000000)) (hi := (481648211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809370114413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809370114413 / 500000000000) = 1/(500000000000 / 809370114413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (48164821 / 100000000) (481648211 / 1000000000) (Real.log (809370114413 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (809370114413 / 500000000000) = -Real.log (500000000000 / 809370114413) := by
    rw [show ((809370114413 / 500000000000) : ℝ) = ((500000000000 / 809370114413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0381

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0382Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0382
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

theorem reflection_log_1_neg : (102266981 / 500000000) ≤ -Real.log (2560 / 3141) ∧
    -Real.log (2560 / 3141) ≤ (204533963 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 5701)) (n := 12)
    (lo := (102266981 / 500000000)) (hi := (204533963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3141 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3141 / 2560) = 1/(2560 / 3141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (102266981 / 500000000) (204533963 / 1000000000) (Real.log (3141 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3141 / 2560) = -Real.log (2560 / 3141) := by
    rw [show ((3141 / 2560) : ℝ) = ((2560 / 3141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (257415591 / 1000000000) ≤ -Real.log (1979 / 2560) ∧
    -Real.log (1979 / 2560) ≤ (32176949 / 125000000) := by
  have h := checkLog_sound (w := (581 / 4539)) (n := 12)
    (lo := (257415591 / 1000000000)) (hi := (32176949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1979) = 1/(1979 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-32176949 / 125000000) (-257415591 / 1000000000) (Real.log (1979 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (51073789 / 250000000) ≤ -Real.log (10240 / 12561) ∧
    -Real.log (10240 / 12561) ≤ (204295157 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 22801)) (n := 12)
    (lo := (51073789 / 250000000)) (hi := (204295157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12561 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12561 / 10240) = 1/(10240 / 12561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (51073789 / 250000000) (204295157 / 1000000000) (Real.log (12561 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12561 / 10240) = -Real.log (10240 / 12561) := by
    rw [show ((12561 / 10240) : ℝ) = ((10240 / 12561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (64259171 / 250000000) ≤ -Real.log (7919 / 10240) ∧
    -Real.log (7919 / 10240) ≤ (51407337 / 200000000) := by
  have h := checkLog_sound (w := (2321 / 18159)) (n := 12)
    (lo := (64259171 / 250000000)) (hi := (51407337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7919) = 1/(7919 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-51407337 / 200000000) (-64259171 / 250000000) (Real.log (7919 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (374253899 / 1000000000) ≤ -Real.log (1280 / 1861) ∧
    -Real.log (1280 / 1861) ≤ (3742539 / 10000000) := by
  have h := checkLog_sound (w := (581 / 3141)) (n := 12)
    (lo := (374253899 / 1000000000)) (hi := (3742539 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1861 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1861 / 1280) = 1/(1280 / 1861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (374253899 / 1000000000) (3742539 / 10000000) (Real.log (1861 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1861 / 1280) = -Real.log (1280 / 1861) := by
    rw [show ((1861 / 1280) : ℝ) = ((1280 / 1861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (302482307 / 500000000) ≤ -Real.log (699 / 1280) ∧
    -Real.log (699 / 1280) ≤ (120992923 / 200000000) := by
  have h := checkLog_sound (w := (581 / 1979)) (n := 12)
    (lo := (302482307 / 500000000)) (hi := (120992923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 699) = 1/(699 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-120992923 / 200000000) (-302482307 / 500000000) (Real.log (699 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (373850809 / 1000000000) ≤ -Real.log (5120 / 7441) ∧
    -Real.log (5120 / 7441) ≤ (37385081 / 100000000) := by
  have h := checkLog_sound (w := (2321 / 12561)) (n := 12)
    (lo := (373850809 / 1000000000)) (hi := (37385081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7441 / 5120) = 1/(5120 / 7441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (373850809 / 1000000000) (37385081 / 100000000) (Real.log (7441 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7441 / 5120) = -Real.log (5120 / 7441) := by
    rw [show ((7441 / 5120) : ℝ) = ((5120 / 7441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (150973057 / 250000000) ≤ -Real.log (2799 / 5120) ∧
    -Real.log (2799 / 5120) ≤ (603892229 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 7919)) (n := 12)
    (lo := (150973057 / 250000000)) (hi := (603892229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2799) = 1/(2799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-603892229 / 1000000000) (-150973057 / 250000000) (Real.log (2799 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (280319787 / 1000000000) ≤ -Real.log (1000000 / 1323553) ∧
    -Real.log (1000000 / 1323553) ≤ (70079947 / 250000000) := by
  have h := checkLog_sound (w := (323553 / 2323553)) (n := 12)
    (lo := (280319787 / 1000000000)) (hi := (70079947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323553 / 1000000) = 1/(1000000 / 1323553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (280319787 / 1000000000) (70079947 / 250000000) (Real.log (1323553 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1323553 / 1000000) = -Real.log (1000000 / 1323553) := by
    rw [show ((1323553 / 1000000) : ℝ) = ((1000000 / 1323553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (195450589 / 500000000) ≤ -Real.log (676447 / 1000000) ∧
    -Real.log (676447 / 1000000) ≤ (390901179 / 1000000000) := by
  have h := checkLog_sound (w := (323553 / 1676447)) (n := 12)
    (lo := (195450589 / 500000000)) (hi := (390901179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676447) = 1/(676447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-390901179 / 1000000000) (-195450589 / 500000000) (Real.log (676447 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (140321553 / 500000000) ≤ -Real.log (1000000 / 1323981) ∧
    -Real.log (1000000 / 1323981) ≤ (280643107 / 1000000000) := by
  have h := checkLog_sound (w := (323981 / 2323981)) (n := 12)
    (lo := (140321553 / 500000000)) (hi := (280643107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323981 / 1000000) = 1/(1000000 / 1323981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (140321553 / 500000000) (280643107 / 1000000000) (Real.log (1323981 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1323981 / 1000000) = -Real.log (1000000 / 1323981) := by
    rw [show ((1323981 / 1000000) : ℝ) = ((1000000 / 1323981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (24470881 / 62500000) ≤ -Real.log (676019 / 1000000) ∧
    -Real.log (676019 / 1000000) ≤ (391534097 / 1000000000) := by
  have h := checkLog_sound (w := (323981 / 1676019)) (n := 12)
    (lo := (24470881 / 62500000)) (hi := (391534097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676019) = 1/(676019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-391534097 / 1000000000) (-24470881 / 62500000) (Real.log (676019 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52892003 / 250000000) ≤ -Real.log (500000 / 617807) ∧
    -Real.log (500000 / 617807) ≤ (211568013 / 1000000000) := by
  have h := checkLog_sound (w := (117807 / 1117807)) (n := 12)
    (lo := (52892003 / 250000000)) (hi := (211568013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617807 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617807 / 500000) = 1/(500000 / 617807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52892003 / 250000000) (211568013 / 1000000000) (Real.log (617807 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (617807 / 500000) = -Real.log (500000 / 617807) := by
    rw [show ((617807 / 500000) : ℝ) = ((500000 / 617807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268682381 / 1000000000) ≤ -Real.log (382193 / 500000) ∧
    -Real.log (382193 / 500000) ≤ (134341191 / 500000000) := by
  have h := checkLog_sound (w := (117807 / 882193)) (n := 12)
    (lo := (268682381 / 1000000000)) (hi := (134341191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 382193) = 1/(382193 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-134341191 / 500000000) (-268682381 / 1000000000) (Real.log (382193 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4236701 / 20000000) ≤ -Real.log (125000 / 154493) ∧
    -Real.log (125000 / 154493) ≤ (211835051 / 1000000000) := by
  have h := checkLog_sound (w := (29493 / 279493)) (n := 12)
    (lo := (4236701 / 20000000)) (hi := (211835051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154493 / 125000) = 1/(125000 / 154493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4236701 / 20000000) (211835051 / 1000000000) (Real.log (154493 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (154493 / 125000) = -Real.log (125000 / 154493) := by
    rw [show ((154493 / 125000) : ℝ) = ((125000 / 154493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (134557097 / 500000000) ≤ -Real.log (95507 / 125000) ∧
    -Real.log (95507 / 125000) ≤ (53822839 / 200000000) := by
  have h := checkLog_sound (w := (29493 / 220507)) (n := 12)
    (lo := (134557097 / 500000000)) (hi := (53822839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95507) = 1/(95507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-53822839 / 200000000) (-134557097 / 500000000) (Real.log (95507 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (335610483 / 500000000) ≤ -Real.log (125000000000 / 244578104419) ∧
    -Real.log (125000000000 / 244578104419) ≤ (671220967 / 1000000000) := by
  have h := checkLog_sound (w := (119578104419 / 369578104419)) (n := 12)
    (lo := (335610483 / 500000000)) (hi := (671220967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244578104419 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244578104419 / 125000000000) = 1/(125000000000 / 244578104419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (335610483 / 500000000) (671220967 / 1000000000) (Real.log (244578104419 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (244578104419 / 125000000000) = -Real.log (125000000000 / 244578104419) := by
    rw [show ((244578104419 / 125000000000) : ℝ) = ((125000000000 / 244578104419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (672177203 / 1000000000) ≤ -Real.log (250000000000 / 489624182161) ∧
    -Real.log (250000000000 / 489624182161) ≤ (168044301 / 250000000) := by
  have h := checkLog_sound (w := (239624182161 / 739624182161)) (n := 12)
    (lo := (672177203 / 1000000000)) (hi := (168044301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489624182161 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489624182161 / 250000000000) = 1/(250000000000 / 489624182161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (672177203 / 1000000000) (168044301 / 250000000) (Real.log (489624182161 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (489624182161 / 250000000000) = -Real.log (250000000000 / 489624182161) := by
    rw [show ((489624182161 / 250000000000) : ℝ) = ((250000000000 / 489624182161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (240125197 / 500000000) ≤ -Real.log (500000000000 / 808239554361) ∧
    -Real.log (500000000000 / 808239554361) ≤ (96050079 / 200000000) := by
  have h := checkLog_sound (w := (308239554361 / 1308239554361)) (n := 12)
    (lo := (240125197 / 500000000)) (hi := (96050079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808239554361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808239554361 / 500000000000) = 1/(500000000000 / 808239554361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (240125197 / 500000000) (96050079 / 200000000) (Real.log (808239554361 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (808239554361 / 500000000000) = -Real.log (500000000000 / 808239554361) := by
    rw [show ((808239554361 / 500000000000) : ℝ) = ((500000000000 / 808239554361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (120237311 / 250000000) ≤ -Real.log (3125000000 / 5055028689) ∧
    -Real.log (3125000000 / 5055028689) ≤ (96189849 / 200000000) := by
  have h := checkLog_sound (w := (1930028689 / 8180028689)) (n := 12)
    (lo := (120237311 / 250000000)) (hi := (96189849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5055028689 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5055028689 / 3125000000) = 1/(3125000000 / 5055028689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (120237311 / 250000000) (96189849 / 200000000) (Real.log (5055028689 / 3125000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5055028689 / 3125000000) = -Real.log (3125000000 / 5055028689) := by
    rw [show ((5055028689 / 3125000000) : ℝ) = ((3125000000 / 5055028689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0382

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0383Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0383
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

theorem reflection_log_1_neg : (51073789 / 250000000) ≤ -Real.log (10240 / 12561) ∧
    -Real.log (10240 / 12561) ≤ (204295157 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 22801)) (n := 12)
    (lo := (51073789 / 250000000)) (hi := (204295157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12561 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12561 / 10240) = 1/(10240 / 12561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (51073789 / 250000000) (204295157 / 1000000000) (Real.log (12561 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12561 / 10240) = -Real.log (10240 / 12561) := by
    rw [show ((12561 / 10240) : ℝ) = ((10240 / 12561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (64259171 / 250000000) ≤ -Real.log (7919 / 10240) ∧
    -Real.log (7919 / 10240) ≤ (51407337 / 200000000) := by
  have h := checkLog_sound (w := (2321 / 18159)) (n := 12)
    (lo := (64259171 / 250000000)) (hi := (51407337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7919) = 1/(7919 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-51407337 / 200000000) (-64259171 / 250000000) (Real.log (7919 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (204056293 / 1000000000) ≤ -Real.log (5120 / 6279) ∧
    -Real.log (5120 / 6279) ≤ (102028147 / 500000000) := by
  have h := checkLog_sound (w := (1159 / 11399)) (n := 12)
    (lo := (204056293 / 1000000000)) (hi := (102028147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 5120) = 1/(5120 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (204056293 / 1000000000) (102028147 / 500000000) (Real.log (6279 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6279 / 5120) = -Real.log (5120 / 6279) := by
    rw [show ((6279 / 5120) : ℝ) = ((5120 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (100257 / 390625) ≤ -Real.log (3961 / 5120) ∧
    -Real.log (3961 / 5120) ≤ (256657921 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 9081)) (n := 12)
    (lo := (100257 / 390625)) (hi := (256657921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3961) = 1/(3961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-256657921 / 1000000000) (-100257 / 390625) (Real.log (3961 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (373850809 / 1000000000) ≤ -Real.log (5120 / 7441) ∧
    -Real.log (5120 / 7441) ≤ (37385081 / 100000000) := by
  have h := checkLog_sound (w := (2321 / 12561)) (n := 12)
    (lo := (373850809 / 1000000000)) (hi := (37385081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7441 / 5120) = 1/(5120 / 7441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (373850809 / 1000000000) (37385081 / 100000000) (Real.log (7441 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7441 / 5120) = -Real.log (5120 / 7441) := by
    rw [show ((7441 / 5120) : ℝ) = ((5120 / 7441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150973057 / 250000000) ≤ -Real.log (2799 / 5120) ∧
    -Real.log (2799 / 5120) ≤ (603892229 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 7919)) (n := 12)
    (lo := (150973057 / 250000000)) (hi := (603892229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2799) = 1/(2799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-603892229 / 1000000000) (-150973057 / 250000000) (Real.log (2799 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93361889 / 250000000) ≤ -Real.log (2560 / 3719) ∧
    -Real.log (2560 / 3719) ≤ (373447557 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 6279)) (n := 12)
    (lo := (93361889 / 250000000)) (hi := (373447557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3719 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3719 / 2560) = 1/(2560 / 3719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93361889 / 250000000) (373447557 / 1000000000) (Real.log (3719 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3719 / 2560) = -Real.log (2560 / 3719) := by
    rw [show ((3719 / 2560) : ℝ) = ((2560 / 3719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (602820991 / 1000000000) ≤ -Real.log (1401 / 2560) ∧
    -Real.log (1401 / 2560) ≤ (4709539 / 7812500) := by
  have h := checkLog_sound (w := (1159 / 3961)) (n := 12)
    (lo := (602820991 / 1000000000)) (hi := (4709539 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1401) = 1/(1401 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4709539 / 7812500) (-602820991 / 1000000000) (Real.log (1401 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139998937 / 500000000) ≤ -Real.log (1000000 / 1323127) ∧
    -Real.log (1000000 / 1323127) ≤ (2239983 / 8000000) := by
  have h := checkLog_sound (w := (323127 / 2323127)) (n := 12)
    (lo := (139998937 / 500000000)) (hi := (2239983 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323127 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323127 / 1000000) = 1/(1000000 / 1323127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139998937 / 500000000) (2239983 / 8000000) (Real.log (1323127 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1323127 / 1000000) = -Real.log (1000000 / 1323127) := by
    rw [show ((1323127 / 1000000) : ℝ) = ((1000000 / 1323127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (78054323 / 200000000) ≤ -Real.log (676873 / 1000000) ∧
    -Real.log (676873 / 1000000) ≤ (3048997 / 7812500) := by
  have h := checkLog_sound (w := (323127 / 1676873)) (n := 12)
    (lo := (78054323 / 200000000)) (hi := (3048997 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676873) = 1/(676873 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3048997 / 7812500) (-78054323 / 200000000) (Real.log (676873 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (140160271 / 500000000) ≤ -Real.log (500000 / 661777) ∧
    -Real.log (500000 / 661777) ≤ (280320543 / 1000000000) := by
  have h := checkLog_sound (w := (161777 / 1161777)) (n := 12)
    (lo := (140160271 / 500000000)) (hi := (280320543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661777 / 500000) = 1/(500000 / 661777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (140160271 / 500000000) (280320543 / 1000000000) (Real.log (661777 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (661777 / 500000) = -Real.log (500000 / 661777) := by
    rw [show ((661777 / 500000) : ℝ) = ((500000 / 661777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (390902657 / 1000000000) ≤ -Real.log (338223 / 500000) ∧
    -Real.log (338223 / 500000) ≤ (195451329 / 500000000) := by
  have h := checkLog_sound (w := (161777 / 838223)) (n := 12)
    (lo := (390902657 / 1000000000)) (hi := (195451329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 338223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 338223) = 1/(338223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195451329 / 500000000) (-390902657 / 1000000000) (Real.log (338223 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13206357 / 62500000) ≤ -Real.log (200000 / 247057) ∧
    -Real.log (200000 / 247057) ≤ (211301713 / 1000000000) := by
  have h := checkLog_sound (w := (47057 / 447057)) (n := 12)
    (lo := (13206357 / 62500000)) (hi := (211301713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247057 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247057 / 200000) = 1/(200000 / 247057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13206357 / 62500000) (211301713 / 1000000000) (Real.log (247057 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247057 / 200000) = -Real.log (200000 / 247057) := by
    rw [show ((247057 / 200000) : ℝ) = ((200000 / 247057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268252063 / 1000000000) ≤ -Real.log (152943 / 200000) ∧
    -Real.log (152943 / 200000) ≤ (8382877 / 31250000) := by
  have h := checkLog_sound (w := (47057 / 352943)) (n := 12)
    (lo := (268252063 / 1000000000)) (hi := (8382877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152943) = 1/(152943 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8382877 / 31250000) (-268252063 / 1000000000) (Real.log (152943 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (211568821 / 1000000000) ≤ -Real.log (200000 / 247123) ∧
    -Real.log (200000 / 247123) ≤ (105784411 / 500000000) := by
  have h := checkLog_sound (w := (47123 / 447123)) (n := 12)
    (lo := (211568821 / 1000000000)) (hi := (105784411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247123 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247123 / 200000) = 1/(200000 / 247123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (211568821 / 1000000000) (105784411 / 500000000) (Real.log (247123 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247123 / 200000) = -Real.log (200000 / 247123) := by
    rw [show ((247123 / 200000) : ℝ) = ((200000 / 247123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (26868369 / 100000000) ≤ -Real.log (152877 / 200000) ∧
    -Real.log (152877 / 200000) ≤ (268683691 / 1000000000) := by
  have h := checkLog_sound (w := (47123 / 352877)) (n := 12)
    (lo := (26868369 / 100000000)) (hi := (268683691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152877) = 1/(152877 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-268683691 / 1000000000) (-26868369 / 100000000) (Real.log (152877 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (67026949 / 100000000) ≤ -Real.log (100000000000 / 195476403993) ∧
    -Real.log (100000000000 / 195476403993) ≤ (670269491 / 1000000000) := by
  have h := checkLog_sound (w := (95476403993 / 295476403993)) (n := 12)
    (lo := (67026949 / 100000000)) (hi := (670269491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195476403993 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195476403993 / 100000000000) = 1/(100000000000 / 195476403993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (67026949 / 100000000) (670269491 / 1000000000) (Real.log (195476403993 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (195476403993 / 100000000000) = -Real.log (100000000000 / 195476403993) := by
    rw [show ((195476403993 / 100000000000) : ℝ) = ((100000000000 / 195476403993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (671223199 / 1000000000) ≤ -Real.log (31250000000 / 61144662693) ∧
    -Real.log (31250000000 / 61144662693) ≤ (839029 / 1250000) := by
  have h := checkLog_sound (w := (29894662693 / 92394662693)) (n := 12)
    (lo := (671223199 / 1000000000)) (hi := (839029 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61144662693 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61144662693 / 31250000000) = 1/(31250000000 / 61144662693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (671223199 / 1000000000) (839029 / 1250000) (Real.log (61144662693 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (61144662693 / 31250000000) = -Real.log (31250000000 / 61144662693) := by
    rw [show ((61144662693 / 31250000000) : ℝ) = ((31250000000 / 61144662693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29972111 / 62500000) ≤ -Real.log (250000000000 / 403838358081) ∧
    -Real.log (250000000000 / 403838358081) ≤ (479553777 / 1000000000) := by
  have h := checkLog_sound (w := (153838358081 / 653838358081)) (n := 12)
    (lo := (29972111 / 62500000)) (hi := (479553777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403838358081 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403838358081 / 250000000000) = 1/(250000000000 / 403838358081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (29972111 / 62500000) (479553777 / 1000000000) (Real.log (403838358081 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (403838358081 / 250000000000) = -Real.log (250000000000 / 403838358081) := by
    rw [show ((403838358081 / 250000000000) : ℝ) = ((250000000000 / 403838358081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (480252511 / 1000000000) ≤ -Real.log (100000000000 / 161648253171) ∧
    -Real.log (100000000000 / 161648253171) ≤ (15007891 / 31250000) := by
  have h := checkLog_sound (w := (61648253171 / 261648253171)) (n := 12)
    (lo := (480252511 / 1000000000)) (hi := (15007891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161648253171 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161648253171 / 100000000000) = 1/(100000000000 / 161648253171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (480252511 / 1000000000) (15007891 / 31250000) (Real.log (161648253171 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (161648253171 / 100000000000) = -Real.log (100000000000 / 161648253171) := by
    rw [show ((161648253171 / 100000000000) : ℝ) = ((100000000000 / 161648253171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0383

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0384Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0384
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

theorem reflection_log_1_neg : (204056293 / 1000000000) ≤ -Real.log (5120 / 6279) ∧
    -Real.log (5120 / 6279) ≤ (102028147 / 500000000) := by
  have h := checkLog_sound (w := (1159 / 11399)) (n := 12)
    (lo := (204056293 / 1000000000)) (hi := (102028147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 5120) = 1/(5120 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (204056293 / 1000000000) (102028147 / 500000000) (Real.log (6279 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6279 / 5120) = -Real.log (5120 / 6279) := by
    rw [show ((6279 / 5120) : ℝ) = ((5120 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (100257 / 390625) ≤ -Real.log (3961 / 5120) ∧
    -Real.log (3961 / 5120) ≤ (256657921 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 9081)) (n := 12)
    (lo := (100257 / 390625)) (hi := (256657921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3961) = 1/(3961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-256657921 / 1000000000) (-100257 / 390625) (Real.log (3961 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50954343 / 250000000) ≤ -Real.log (2048 / 2511) ∧
    -Real.log (2048 / 2511) ≤ (203817373 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 4559)) (n := 12)
    (lo := (50954343 / 250000000)) (hi := (203817373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2511 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2511 / 2048) = 1/(2048 / 2511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50954343 / 250000000) (203817373 / 1000000000) (Real.log (2511 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2511 / 2048) = -Real.log (2048 / 2511) := by
    rw [show ((2511 / 2048) : ℝ) = ((2048 / 2511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (256279299 / 1000000000) ≤ -Real.log (1585 / 2048) ∧
    -Real.log (1585 / 2048) ≤ (2562793 / 10000000) := by
  have h := checkLog_sound (w := (463 / 3633)) (n := 12)
    (lo := (256279299 / 1000000000)) (hi := (2562793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1585) = 1/(1585 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2562793 / 10000000) (-256279299 / 1000000000) (Real.log (1585 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93361889 / 250000000) ≤ -Real.log (2560 / 3719) ∧
    -Real.log (2560 / 3719) ≤ (373447557 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 6279)) (n := 12)
    (lo := (93361889 / 250000000)) (hi := (373447557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3719 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3719 / 2560) = 1/(2560 / 3719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93361889 / 250000000) (373447557 / 1000000000) (Real.log (3719 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3719 / 2560) = -Real.log (2560 / 3719) := by
    rw [show ((3719 / 2560) : ℝ) = ((2560 / 3719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (602820991 / 1000000000) ≤ -Real.log (1401 / 2560) ∧
    -Real.log (1401 / 2560) ≤ (4709539 / 7812500) := by
  have h := checkLog_sound (w := (1159 / 3961)) (n := 12)
    (lo := (602820991 / 1000000000)) (hi := (4709539 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1401) = 1/(1401 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4709539 / 7812500) (-602820991 / 1000000000) (Real.log (1401 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18652207 / 50000000) ≤ -Real.log (1024 / 1487) ∧
    -Real.log (1024 / 1487) ≤ (373044141 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2511)) (n := 12)
    (lo := (18652207 / 50000000)) (hi := (373044141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487 / 1024) = 1/(1024 / 1487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18652207 / 50000000) (373044141 / 1000000000) (Real.log (1487 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1487 / 1024) = -Real.log (1024 / 1487) := by
    rw [show ((1487 / 1024) : ℝ) = ((1024 / 1487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6017509 / 10000000) ≤ -Real.log (561 / 1024) ∧
    -Real.log (561 / 1024) ≤ (601750901 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1585)) (n := 12)
    (lo := (6017509 / 10000000)) (hi := (601750901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 561) = 1/(561 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-601750901 / 1000000000) (-6017509 / 10000000) (Real.log (561 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139837551 / 500000000) ≤ -Real.log (10000 / 13227) ∧
    -Real.log (10000 / 13227) ≤ (279675103 / 1000000000) := by
  have h := checkLog_sound (w := (3227 / 23227)) (n := 12)
    (lo := (139837551 / 500000000)) (hi := (279675103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13227 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13227 / 10000) = 1/(10000 / 13227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139837551 / 500000000) (279675103 / 1000000000) (Real.log (13227 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (13227 / 10000) = -Real.log (10000 / 13227) := by
    rw [show ((13227 / 10000) : ℝ) = ((10000 / 13227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (97410243 / 250000000) ≤ -Real.log (6773 / 10000) ∧
    -Real.log (6773 / 10000) ≤ (389640973 / 1000000000) := by
  have h := checkLog_sound (w := (3227 / 16773)) (n := 12)
    (lo := (97410243 / 250000000)) (hi := (389640973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 6773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 6773) = 1/(6773 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-389640973 / 1000000000) (-97410243 / 250000000) (Real.log (6773 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (27999863 / 100000000) ≤ -Real.log (125000 / 165391) ∧
    -Real.log (125000 / 165391) ≤ (279998631 / 1000000000) := by
  have h := checkLog_sound (w := (40391 / 290391)) (n := 12)
    (lo := (27999863 / 100000000)) (hi := (279998631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165391 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165391 / 125000) = 1/(125000 / 165391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (27999863 / 100000000) (279998631 / 1000000000) (Real.log (165391 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165391 / 125000) = -Real.log (125000 / 165391) := by
    rw [show ((165391 / 125000) : ℝ) = ((125000 / 165391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (390273093 / 1000000000) ≤ -Real.log (84609 / 125000) ∧
    -Real.log (84609 / 125000) ≤ (195136547 / 500000000) := by
  have h := checkLog_sound (w := (40391 / 209609)) (n := 12)
    (lo := (390273093 / 1000000000)) (hi := (195136547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84609) = 1/(84609 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195136547 / 500000000) (-390273093 / 1000000000) (Real.log (84609 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (211035341 / 1000000000) ≤ -Real.log (250000 / 308739) ∧
    -Real.log (250000 / 308739) ≤ (105517671 / 500000000) := by
  have h := checkLog_sound (w := (58739 / 558739)) (n := 12)
    (lo := (211035341 / 1000000000)) (hi := (105517671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308739 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308739 / 250000) = 1/(250000 / 308739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (211035341 / 1000000000) (105517671 / 500000000) (Real.log (308739 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (308739 / 250000) = -Real.log (250000 / 308739) := by
    rw [show ((308739 / 250000) : ℝ) = ((250000 / 308739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26782193 / 100000000) ≤ -Real.log (191261 / 250000) ∧
    -Real.log (191261 / 250000) ≤ (267821931 / 1000000000) := by
  have h := checkLog_sound (w := (58739 / 441261)) (n := 12)
    (lo := (26782193 / 100000000)) (hi := (267821931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191261) = 1/(191261 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-267821931 / 1000000000) (-26782193 / 100000000) (Real.log (191261 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (105651261 / 500000000) ≤ -Real.log (500000 / 617643) ∧
    -Real.log (500000 / 617643) ≤ (211302523 / 1000000000) := by
  have h := checkLog_sound (w := (117643 / 1117643)) (n := 12)
    (lo := (105651261 / 500000000)) (hi := (211302523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617643 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617643 / 500000) = 1/(500000 / 617643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (105651261 / 500000000) (211302523 / 1000000000) (Real.log (617643 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (617643 / 500000) = -Real.log (500000 / 617643) := by
    rw [show ((617643 / 500000) : ℝ) = ((500000 / 617643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (268253371 / 1000000000) ≤ -Real.log (382357 / 500000) ∧
    -Real.log (382357 / 500000) ≤ (67063343 / 250000000) := by
  have h := checkLog_sound (w := (117643 / 882357)) (n := 12)
    (lo := (268253371 / 1000000000)) (hi := (67063343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 382357) = 1/(382357 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-67063343 / 250000000) (-268253371 / 1000000000) (Real.log (382357 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (334658037 / 500000000) ≤ -Real.log (500000000000 / 976450612727) ∧
    -Real.log (500000000000 / 976450612727) ≤ (26772643 / 40000000) := by
  have h := checkLog_sound (w := (476450612727 / 1476450612727)) (n := 12)
    (lo := (334658037 / 500000000)) (hi := (26772643 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976450612727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976450612727 / 500000000000) = 1/(500000000000 / 976450612727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (334658037 / 500000000) (26772643 / 40000000) (Real.log (976450612727 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (976450612727 / 500000000000) = -Real.log (500000000000 / 976450612727) := by
    rw [show ((976450612727 / 500000000000) : ℝ) = ((500000000000 / 976450612727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (670271723 / 1000000000) ≤ -Real.log (500000000000 / 977384202627) ∧
    -Real.log (500000000000 / 977384202627) ≤ (167567931 / 250000000) := by
  have h := checkLog_sound (w := (477384202627 / 1477384202627)) (n := 12)
    (lo := (670271723 / 1000000000)) (hi := (167567931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977384202627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977384202627 / 500000000000) = 1/(500000000000 / 977384202627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (670271723 / 1000000000) (167567931 / 250000000) (Real.log (977384202627 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (977384202627 / 500000000000) = -Real.log (500000000000 / 977384202627) := by
    rw [show ((977384202627 / 500000000000) : ℝ) = ((500000000000 / 977384202627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (59857159 / 125000000) ≤ -Real.log (500000000000 / 807114362049) ∧
    -Real.log (500000000000 / 807114362049) ≤ (478857273 / 1000000000) := by
  have h := checkLog_sound (w := (307114362049 / 1307114362049)) (n := 12)
    (lo := (59857159 / 125000000)) (hi := (478857273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807114362049 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807114362049 / 500000000000) = 1/(500000000000 / 807114362049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (59857159 / 125000000) (478857273 / 1000000000) (Real.log (807114362049 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (807114362049 / 500000000000) = -Real.log (500000000000 / 807114362049) := by
    rw [show ((807114362049 / 500000000000) : ℝ) = ((500000000000 / 807114362049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (479555893 / 1000000000) ≤ -Real.log (500000000000 / 807678426183) ∧
    -Real.log (500000000000 / 807678426183) ≤ (239777947 / 500000000) := by
  have h := checkLog_sound (w := (307678426183 / 1307678426183)) (n := 12)
    (lo := (479555893 / 1000000000)) (hi := (239777947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807678426183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807678426183 / 500000000000) = 1/(500000000000 / 807678426183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (479555893 / 1000000000) (239777947 / 500000000) (Real.log (807678426183 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (807678426183 / 500000000000) = -Real.log (500000000000 / 807678426183) := by
    rw [show ((807678426183 / 500000000000) : ℝ) = ((500000000000 / 807678426183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0384

end


