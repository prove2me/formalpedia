-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0087Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0087Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:03:37.02557+00:00
-- url     : https://prove2.me/theorems/e96acd60-8c8d-4c7c-94e5-ee1b6f448db3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0087Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0088Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0087Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0088Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0089Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0090Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0091Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0092Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0087Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0088Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0089Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0090Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0091Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0092Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0087Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0088Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0089Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0090Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0091Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0092Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0087Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0088Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0089Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0090Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0091Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0092Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0087Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0087
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

theorem reflection_log_1_neg : (344254377 / 1000000000) ≤ -Real.log (640 / 903) ∧
    -Real.log (640 / 903) ≤ (172127189 / 500000000) := by
  have h := checkLog_sound (w := (263 / 1543)) (n := 12)
    (lo := (344254377 / 1000000000)) (hi := (172127189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903 / 640) = 1/(640 / 903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (344254377 / 1000000000) (172127189 / 500000000) (Real.log (903 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (903 / 640) = -Real.log (640 / 903) := by
    rw [show ((903 / 640) : ℝ) = ((640 / 903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (132305747 / 250000000) ≤ -Real.log (377 / 640) ∧
    -Real.log (377 / 640) ≤ (529222989 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 1017)) (n := 12)
    (lo := (132305747 / 250000000)) (hi := (529222989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 377) = 1/(377 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-529222989 / 1000000000) (-132305747 / 250000000) (Real.log (377 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (343423467 / 1000000000) ≤ -Real.log (2560 / 3609) ∧
    -Real.log (2560 / 3609) ≤ (85855867 / 250000000) := by
  have h := checkLog_sound (w := (1049 / 6169)) (n := 12)
    (lo := (343423467 / 1000000000)) (hi := (85855867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3609 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3609 / 2560) = 1/(2560 / 3609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (343423467 / 1000000000) (85855867 / 250000000) (Real.log (3609 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3609 / 2560) = -Real.log (2560 / 3609) := by
    rw [show ((3609 / 2560) : ℝ) = ((2560 / 3609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (21089423 / 40000000) ≤ -Real.log (1511 / 2560) ∧
    -Real.log (1511 / 2560) ≤ (65904447 / 125000000) := by
  have h := checkLog_sound (w := (1049 / 4071)) (n := 12)
    (lo := (21089423 / 40000000)) (hi := (65904447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1511) = 1/(1511 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65904447 / 125000000) (-21089423 / 40000000) (Real.log (1511 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (59986619 / 100000000) ≤ -Real.log (320 / 583) ∧
    -Real.log (320 / 583) ≤ (599866191 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 903)) (n := 12)
    (lo := (59986619 / 100000000)) (hi := (599866191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583 / 320) = 1/(320 / 583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (59986619 / 100000000) (599866191 / 1000000000) (Real.log (583 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (583 / 320) = -Real.log (320 / 583) := by
    rw [show ((583 / 320) : ℝ) = ((320 / 583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (862634863 / 500000000) ≤ -Real.log (57 / 320) ∧
    -Real.log (57 / 320) ≤ (1725269729 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 57) = 1/(57 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1725269729 / 1000000000) (-862634863 / 500000000) (Real.log (57 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18705591 / 31250000) ≤ -Real.log (1280 / 2329) ∧
    -Real.log (1280 / 2329) ≤ (598578913 / 1000000000) := by
  have h := checkLog_sound (w := (1049 / 3609)) (n := 12)
    (lo := (18705591 / 31250000)) (hi := (598578913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2329 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2329 / 1280) = 1/(1280 / 2329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18705591 / 31250000) (598578913 / 1000000000) (Real.log (2329 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2329 / 1280) = -Real.log (1280 / 2329) := by
    rw [show ((2329 / 1280) : ℝ) = ((1280 / 2329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (342439529 / 200000000) ≤ -Real.log (231 / 1280) ∧
    -Real.log (231 / 1280) ≤ (107012353 / 62500000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 231) = 1/(231 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-107012353 / 62500000) (-342439529 / 200000000) (Real.log (231 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59007221 / 125000000) ≤ -Real.log (100000 / 160329) ∧
    -Real.log (100000 / 160329) ≤ (472057769 / 1000000000) := by
  have h := checkLog_sound (w := (60329 / 260329)) (n := 12)
    (lo := (59007221 / 125000000)) (hi := (472057769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160329 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160329 / 100000) = 1/(100000 / 160329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59007221 / 125000000) (472057769 / 1000000000) (Real.log (160329 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160329 / 100000) = -Real.log (100000 / 160329) := by
    rw [show ((160329 / 100000) : ℝ) = ((100000 / 160329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (924549743 / 1000000000) ≤ -Real.log (39671 / 100000) ∧
    -Real.log (39671 / 100000) ≤ (184909949 / 200000000) := by
  have h := checkLog_sound (w := (10329 / 89671)) (n := 12)
    (lo := (231402563 / 1000000000)) (hi := (57850641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39671) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 39671) = 1/(39671 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-184909949 / 200000000) (-924549743 / 1000000000) (Real.log (39671 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (473267671 / 1000000000) ≤ -Real.log (1000000 / 1605231) ∧
    -Real.log (1000000 / 1605231) ≤ (59158459 / 125000000) := by
  have h := checkLog_sound (w := (605231 / 2605231)) (n := 12)
    (lo := (473267671 / 1000000000)) (hi := (59158459 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1605231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1605231 / 1000000) = 1/(1000000 / 1605231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (473267671 / 1000000000) (59158459 / 125000000) (Real.log (1605231 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1605231 / 1000000) = -Real.log (1000000 / 1605231) := by
    rw [show ((1605231 / 1000000) : ℝ) = ((1000000 / 1605231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (464727247 / 500000000) ≤ -Real.log (394769 / 1000000) ∧
    -Real.log (394769 / 1000000) ≤ (29045453 / 31250000) := by
  have h := checkLog_sound (w := (105231 / 894769)) (n := 12)
    (lo := (118153657 / 500000000)) (hi := (47261463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 394769) = 1/(394769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-29045453 / 31250000) (-464727247 / 500000000) (Real.log (394769 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (387969617 / 1000000000) ≤ -Real.log (200000 / 294797) ∧
    -Real.log (200000 / 294797) ≤ (193984809 / 500000000) := by
  have h := checkLog_sound (w := (94797 / 494797)) (n := 12)
    (lo := (387969617 / 1000000000)) (hi := (193984809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294797 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294797 / 200000) = 1/(200000 / 294797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (387969617 / 1000000000) (193984809 / 500000000) (Real.log (294797 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (294797 / 200000) = -Real.log (200000 / 294797) := by
    rw [show ((294797 / 200000) : ℝ) = ((200000 / 294797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (642425549 / 1000000000) ≤ -Real.log (105203 / 200000) ∧
    -Real.log (105203 / 200000) ≤ (12848511 / 20000000) := by
  have h := checkLog_sound (w := (94797 / 305203)) (n := 12)
    (lo := (642425549 / 1000000000)) (hi := (12848511 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 105203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 105203) = 1/(105203 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-12848511 / 20000000) (-642425549 / 1000000000) (Real.log (105203 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (48653923 / 125000000) ≤ -Real.log (500000 / 737923) ∧
    -Real.log (500000 / 737923) ≤ (77846277 / 200000000) := by
  have h := checkLog_sound (w := (237923 / 1237923)) (n := 12)
    (lo := (48653923 / 125000000)) (hi := (77846277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737923 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737923 / 500000) = 1/(500000 / 737923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48653923 / 125000000) (77846277 / 200000000) (Real.log (737923 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (737923 / 500000) = -Real.log (500000 / 737923) := by
    rw [show ((737923 / 500000) : ℝ) = ((500000 / 737923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (40373109 / 62500000) ≤ -Real.log (262077 / 500000) ∧
    -Real.log (262077 / 500000) ≤ (129193949 / 200000000) := by
  have h := checkLog_sound (w := (237923 / 762077)) (n := 12)
    (lo := (40373109 / 62500000)) (hi := (129193949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 262077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 262077) = 1/(262077 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-129193949 / 200000000) (-40373109 / 62500000) (Real.log (262077 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (139660751 / 100000000) ≤ -Real.log (125000000000 / 505183257291) ∧
    -Real.log (125000000000 / 505183257291) ≤ (1396607513 / 1000000000) := by
  have h := checkLog_sound (w := (5183257291 / 1005183257291)) (n := 12)
    (lo := (206263 / 20000000)) (hi := (10313151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505183257291 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(505183257291 / 500000000000) = 1/(125000000000 / 505183257291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (139660751 / 100000000) (1396607513 / 1000000000) (Real.log (505183257291 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (505183257291 / 125000000000) = -Real.log (125000000000 / 505183257291) := by
    rw [show ((505183257291 / 125000000000) : ℝ) = ((125000000000 / 505183257291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (280544433 / 200000000) ≤ -Real.log (125000000000 / 508281741981) ∧
    -Real.log (125000000000 / 508281741981) ≤ (175340271 / 125000000) := by
  have h := checkLog_sound (w := (8281741981 / 1008281741981)) (n := 12)
    (lo := (3285561 / 200000000)) (hi := (8213903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508281741981 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(508281741981 / 500000000000) = 1/(125000000000 / 508281741981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (280544433 / 200000000) (175340271 / 125000000) (Real.log (508281741981 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (508281741981 / 125000000000) = -Real.log (125000000000 / 508281741981) := by
    rw [show ((508281741981 / 125000000000) : ℝ) = ((125000000000 / 508281741981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (515197583 / 500000000) ≤ -Real.log (250000000000 / 700543235459) ∧
    -Real.log (250000000000 / 700543235459) ≤ (32199849 / 31250000) := by
  have h := checkLog_sound (w := (200543235459 / 1200543235459)) (n := 12)
    (lo := (168623993 / 500000000)) (hi := (337247987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700543235459 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(700543235459 / 500000000000) = 1/(250000000000 / 700543235459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (515197583 / 500000000) (32199849 / 31250000) (Real.log (700543235459 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (700543235459 / 250000000000) = -Real.log (250000000000 / 700543235459) := by
    rw [show ((700543235459 / 250000000000) : ℝ) = ((250000000000 / 700543235459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (129400141 / 125000000) ≤ -Real.log (2500000000 / 7039181233) ∧
    -Real.log (2500000000 / 7039181233) ≤ (103520113 / 100000000) := by
  have h := checkLog_sound (w := (2039181233 / 12039181233)) (n := 12)
    (lo := (85513487 / 250000000)) (hi := (342053949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7039181233 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7039181233 / 5000000000) = 1/(2500000000 / 7039181233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (129400141 / 125000000) (103520113 / 100000000) (Real.log (7039181233 / 2500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7039181233 / 2500000000) = -Real.log (2500000000 / 7039181233) := by
    rw [show ((7039181233 / 2500000000) : ℝ) = ((2500000000 / 7039181233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0087

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0088Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0088
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

theorem reflection_log_1_neg : (343423467 / 1000000000) ≤ -Real.log (2560 / 3609) ∧
    -Real.log (2560 / 3609) ≤ (85855867 / 250000000) := by
  have h := checkLog_sound (w := (1049 / 6169)) (n := 12)
    (lo := (343423467 / 1000000000)) (hi := (85855867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3609 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3609 / 2560) = 1/(2560 / 3609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (343423467 / 1000000000) (85855867 / 250000000) (Real.log (3609 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3609 / 2560) = -Real.log (2560 / 3609) := by
    rw [show ((3609 / 2560) : ℝ) = ((2560 / 3609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (21089423 / 40000000) ≤ -Real.log (1511 / 2560) ∧
    -Real.log (1511 / 2560) ≤ (65904447 / 125000000) := by
  have h := checkLog_sound (w := (1049 / 4071)) (n := 12)
    (lo := (21089423 / 40000000)) (hi := (65904447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1511) = 1/(1511 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65904447 / 125000000) (-21089423 / 40000000) (Real.log (1511 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (171295933 / 500000000) ≤ -Real.log (1280 / 1803) ∧
    -Real.log (1280 / 1803) ≤ (342591867 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 3083)) (n := 12)
    (lo := (171295933 / 500000000)) (hi := (342591867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1803 / 1280) = 1/(1280 / 1803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (171295933 / 500000000) (342591867 / 1000000000) (Real.log (1803 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1803 / 1280) = -Real.log (1280 / 1803) := by
    rw [show ((1803 / 1280) : ℝ) = ((1280 / 1803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (525252103 / 1000000000) ≤ -Real.log (757 / 1280) ∧
    -Real.log (757 / 1280) ≤ (65656513 / 125000000) := by
  have h := checkLog_sound (w := (523 / 2037)) (n := 12)
    (lo := (525252103 / 1000000000)) (hi := (65656513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 757) = 1/(757 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65656513 / 125000000) (-525252103 / 1000000000) (Real.log (757 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18705591 / 31250000) ≤ -Real.log (1280 / 2329) ∧
    -Real.log (1280 / 2329) ≤ (598578913 / 1000000000) := by
  have h := checkLog_sound (w := (1049 / 3609)) (n := 12)
    (lo := (18705591 / 31250000)) (hi := (598578913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2329 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2329 / 1280) = 1/(1280 / 2329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18705591 / 31250000) (598578913 / 1000000000) (Real.log (2329 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2329 / 1280) = -Real.log (1280 / 2329) := by
    rw [show ((2329 / 1280) : ℝ) = ((1280 / 2329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (342439529 / 200000000) ≤ -Real.log (231 / 1280) ∧
    -Real.log (231 / 1280) ≤ (107012353 / 62500000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 231) = 1/(231 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-107012353 / 62500000) (-342439529 / 200000000) (Real.log (231 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (74661247 / 125000000) ≤ -Real.log (640 / 1163) ∧
    -Real.log (640 / 1163) ≤ (597289977 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 1803)) (n := 12)
    (lo := (74661247 / 125000000)) (hi := (597289977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163 / 640) = 1/(640 / 1163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (74661247 / 125000000) (597289977 / 1000000000) (Real.log (1163 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1163 / 640) = -Real.log (640 / 1163) := by
    rw [show ((1163 / 640) : ℝ) = ((640 / 1163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10620589 / 6250000) ≤ -Real.log (117 / 640) ∧
    -Real.log (117 / 640) ≤ (1699294243 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 117) = 1/(117 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1699294243 / 1000000000) (-10620589 / 6250000) (Real.log (117 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29428017 / 62500000) ≤ -Real.log (125000 / 200169) ∧
    -Real.log (125000 / 200169) ≤ (470848273 / 1000000000) := by
  have h := checkLog_sound (w := (75169 / 325169)) (n := 12)
    (lo := (29428017 / 62500000)) (hi := (470848273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200169 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200169 / 125000) = 1/(125000 / 200169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29428017 / 62500000) (470848273 / 1000000000) (Real.log (200169 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (200169 / 125000) = -Real.log (125000 / 200169) := by
    rw [show ((200169 / 125000) : ℝ) = ((125000 / 200169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (114959557 / 125000000) ≤ -Real.log (49831 / 125000) ∧
    -Real.log (49831 / 125000) ≤ (459838229 / 500000000) := by
  have h := checkLog_sound (w := (12669 / 112331)) (n := 12)
    (lo := (56632319 / 250000000)) (hi := (226529277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 49831) = 1/(49831 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-459838229 / 500000000) (-114959557 / 125000000) (Real.log (49831 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (472058391 / 1000000000) ≤ -Real.log (1000000 / 1603291) ∧
    -Real.log (1000000 / 1603291) ≤ (59007299 / 125000000) := by
  have h := checkLog_sound (w := (603291 / 2603291)) (n := 12)
    (lo := (472058391 / 1000000000)) (hi := (59007299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603291 / 1000000) = 1/(1000000 / 1603291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (472058391 / 1000000000) (59007299 / 125000000) (Real.log (1603291 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1603291 / 1000000) = -Real.log (1000000 / 1603291) := by
    rw [show ((1603291 / 1000000) : ℝ) = ((1000000 / 1603291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (924552263 / 1000000000) ≤ -Real.log (396709 / 1000000) ∧
    -Real.log (396709 / 1000000) ≤ (184910453 / 200000000) := by
  have h := checkLog_sound (w := (103291 / 896709)) (n := 12)
    (lo := (231405083 / 1000000000)) (hi := (57851271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396709) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 396709) = 1/(396709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-184910453 / 200000000) (-924552263 / 1000000000) (Real.log (396709 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38671101 / 100000000) ≤ -Real.log (1000000 / 1472131) ∧
    -Real.log (1000000 / 1472131) ≤ (386711011 / 1000000000) := by
  have h := checkLog_sound (w := (472131 / 2472131)) (n := 12)
    (lo := (38671101 / 100000000)) (hi := (386711011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1472131 / 1000000) = 1/(1000000 / 1472131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38671101 / 100000000) (386711011 / 1000000000) (Real.log (1472131 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1472131 / 1000000) = -Real.log (1000000 / 1472131) := by
    rw [show ((1472131 / 1000000) : ℝ) = ((1000000 / 1472131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (159726783 / 250000000) ≤ -Real.log (527869 / 1000000) ∧
    -Real.log (527869 / 1000000) ≤ (638907133 / 1000000000) := by
  have h := checkLog_sound (w := (472131 / 1527869)) (n := 12)
    (lo := (159726783 / 250000000)) (hi := (638907133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 527869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 527869) = 1/(527869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-638907133 / 1000000000) (-159726783 / 250000000) (Real.log (527869 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (77594059 / 200000000) ≤ -Real.log (500000 / 736993) ∧
    -Real.log (500000 / 736993) ≤ (48496287 / 125000000) := by
  have h := checkLog_sound (w := (236993 / 1236993)) (n := 12)
    (lo := (77594059 / 200000000)) (hi := (48496287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736993 / 500000) = 1/(500000 / 736993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (77594059 / 200000000) (48496287 / 125000000) (Real.log (736993 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (736993 / 500000) = -Real.log (500000 / 736993) := by
    rw [show ((736993 / 500000) : ℝ) = ((500000 / 736993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (12848549 / 20000000) ≤ -Real.log (263007 / 500000) ∧
    -Real.log (263007 / 500000) ≤ (642427451 / 1000000000) := by
  have h := checkLog_sound (w := (236993 / 763007)) (n := 12)
    (lo := (12848549 / 20000000)) (hi := (642427451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 263007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 263007) = 1/(263007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-642427451 / 1000000000) (-12848549 / 20000000) (Real.log (263007 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (173815591 / 125000000) ≤ -Real.log (500000000000 / 2008478657863) ∧
    -Real.log (500000000000 / 2008478657863) ≤ (1390524731 / 1000000000) := by
  have h := checkLog_sound (w := (8478657863 / 4008478657863)) (n := 12)
    (lo := (132199 / 31250000)) (hi := (4230369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2008478657863 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2008478657863 / 2000000000000) = 1/(500000000000 / 2008478657863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173815591 / 125000000) (1390524731 / 1000000000) (Real.log (2008478657863 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2008478657863 / 500000000000) = -Real.log (500000000000 / 2008478657863) := by
    rw [show ((2008478657863 / 500000000000) : ℝ) = ((500000000000 / 2008478657863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (279322131 / 200000000) ≤ -Real.log (125000000000 / 505184845819) ∧
    -Real.log (125000000000 / 505184845819) ≤ (698305329 / 500000000) := by
  have h := checkLog_sound (w := (5184845819 / 1005184845819)) (n := 12)
    (lo := (2063259 / 200000000)) (hi := (1289537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505184845819 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(505184845819 / 500000000000) = 1/(125000000000 / 505184845819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (279322131 / 200000000) (698305329 / 500000000) (Real.log (505184845819 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (505184845819 / 125000000000) = -Real.log (125000000000 / 505184845819) := by
    rw [show ((505184845819 / 125000000000) : ℝ) = ((125000000000 / 505184845819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (512809071 / 500000000) ≤ -Real.log (250000000000 / 697204704197) ∧
    -Real.log (250000000000 / 697204704197) ≤ (32050567 / 31250000) := by
  have h := checkLog_sound (w := (197204704197 / 1197204704197)) (n := 12)
    (lo := (166235481 / 500000000)) (hi := (332470963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697204704197 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(697204704197 / 500000000000) = 1/(250000000000 / 697204704197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (512809071 / 500000000) (32050567 / 31250000) (Real.log (697204704197 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (697204704197 / 250000000000) = -Real.log (250000000000 / 697204704197) := by
    rw [show ((697204704197 / 250000000000) : ℝ) = ((250000000000 / 697204704197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (206079549 / 200000000) ≤ -Real.log (100000000000 / 280218017011) ∧
    -Real.log (100000000000 / 280218017011) ≤ (1030397747 / 1000000000) := by
  have h := checkLog_sound (w := (80218017011 / 480218017011)) (n := 12)
    (lo := (67450113 / 200000000)) (hi := (168625283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280218017011 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(280218017011 / 200000000000) = 1/(100000000000 / 280218017011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (206079549 / 200000000) (1030397747 / 1000000000) (Real.log (280218017011 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (280218017011 / 100000000000) = -Real.log (100000000000 / 280218017011) := by
    rw [show ((280218017011 / 100000000000) : ℝ) = ((100000000000 / 280218017011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0088

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0089Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0089
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

theorem reflection_log_1_neg : (171295933 / 500000000) ≤ -Real.log (1280 / 1803) ∧
    -Real.log (1280 / 1803) ≤ (342591867 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 3083)) (n := 12)
    (lo := (171295933 / 500000000)) (hi := (342591867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1803 / 1280) = 1/(1280 / 1803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (171295933 / 500000000) (342591867 / 1000000000) (Real.log (1803 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1803 / 1280) = -Real.log (1280 / 1803) := by
    rw [show ((1803 / 1280) : ℝ) = ((1280 / 1803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (525252103 / 1000000000) ≤ -Real.log (757 / 1280) ∧
    -Real.log (757 / 1280) ≤ (65656513 / 125000000) := by
  have h := checkLog_sound (w := (523 / 2037)) (n := 12)
    (lo := (525252103 / 1000000000)) (hi := (65656513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 757) = 1/(757 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65656513 / 125000000) (-525252103 / 1000000000) (Real.log (757 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341759573 / 1000000000) ≤ -Real.log (2560 / 3603) ∧
    -Real.log (2560 / 3603) ≤ (170879787 / 500000000) := by
  have h := checkLog_sound (w := (1043 / 6163)) (n := 12)
    (lo := (341759573 / 1000000000)) (hi := (170879787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3603 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3603 / 2560) = 1/(2560 / 3603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341759573 / 1000000000) (170879787 / 500000000) (Real.log (3603 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3603 / 2560) = -Real.log (2560 / 3603) := by
    rw [show ((3603 / 2560) : ℝ) = ((2560 / 3603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (261636279 / 500000000) ≤ -Real.log (1517 / 2560) ∧
    -Real.log (1517 / 2560) ≤ (523272559 / 1000000000) := by
  have h := checkLog_sound (w := (1043 / 4077)) (n := 12)
    (lo := (261636279 / 500000000)) (hi := (523272559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1517) = 1/(1517 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-523272559 / 1000000000) (-261636279 / 500000000) (Real.log (1517 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (74661247 / 125000000) ≤ -Real.log (640 / 1163) ∧
    -Real.log (640 / 1163) ≤ (597289977 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 1803)) (n := 12)
    (lo := (74661247 / 125000000)) (hi := (597289977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163 / 640) = 1/(640 / 1163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (74661247 / 125000000) (597289977 / 1000000000) (Real.log (1163 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1163 / 640) = -Real.log (640 / 1163) := by
    rw [show ((1163 / 640) : ℝ) = ((640 / 1163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10620589 / 6250000) ≤ -Real.log (117 / 640) ∧
    -Real.log (117 / 640) ≤ (1699294243 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 117) = 1/(117 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1699294243 / 1000000000) (-10620589 / 6250000) (Real.log (117 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (953599 / 1600000) ≤ -Real.log (1280 / 2323) ∧
    -Real.log (1280 / 2323) ≤ (37249961 / 62500000) := by
  have h := checkLog_sound (w := (1043 / 3603)) (n := 12)
    (lo := (953599 / 1600000)) (hi := (37249961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2323 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2323 / 1280) = 1/(1280 / 2323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (953599 / 1600000) (37249961 / 62500000) (Real.log (2323 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2323 / 1280) = -Real.log (1280 / 2323) := by
    rw [show ((2323 / 1280) : ℝ) = ((1280 / 2323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (843277607 / 500000000) ≤ -Real.log (237 / 1280) ∧
    -Real.log (237 / 1280) ≤ (1686555217 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 237) = 1/(237 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1686555217 / 1000000000) (-843277607 / 500000000) (Real.log (237 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (234820219 / 500000000) ≤ -Real.log (1000000 / 1599419) ∧
    -Real.log (1000000 / 1599419) ≤ (469640439 / 1000000000) := by
  have h := checkLog_sound (w := (599419 / 2599419)) (n := 12)
    (lo := (234820219 / 500000000)) (hi := (469640439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599419 / 1000000) = 1/(1000000 / 1599419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (234820219 / 500000000) (469640439 / 1000000000) (Real.log (1599419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1599419 / 1000000) = -Real.log (1000000 / 1599419) := by
    rw [show ((1599419 / 1000000) : ℝ) = ((1000000 / 1599419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182967857 / 200000000) ≤ -Real.log (400581 / 1000000) ∧
    -Real.log (400581 / 1000000) ≤ (914839287 / 1000000000) := by
  have h := checkLog_sound (w := (99419 / 900581)) (n := 12)
    (lo := (44338421 / 200000000)) (hi := (110846053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400581) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 400581) = 1/(400581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-914839287 / 1000000000) (-182967857 / 200000000) (Real.log (400581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3678507 / 7812500) ≤ -Real.log (1000000 / 1601353) ∧
    -Real.log (1000000 / 1601353) ≤ (470848897 / 1000000000) := by
  have h := checkLog_sound (w := (601353 / 2601353)) (n := 12)
    (lo := (3678507 / 7812500)) (hi := (470848897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1601353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1601353 / 1000000) = 1/(1000000 / 1601353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3678507 / 7812500) (470848897 / 1000000000) (Real.log (1601353 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1601353 / 1000000) = -Real.log (1000000 / 1601353) := by
    rw [show ((1601353 / 1000000) : ℝ) = ((1000000 / 1601353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (229919741 / 250000000) ≤ -Real.log (398647 / 1000000) ∧
    -Real.log (398647 / 1000000) ≤ (459839483 / 500000000) := by
  have h := checkLog_sound (w := (101353 / 898647)) (n := 12)
    (lo := (28316473 / 125000000)) (hi := (45306357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 398647) = 1/(398647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-459839483 / 500000000) (-229919741 / 250000000) (Real.log (398647 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (385456259 / 1000000000) ≤ -Real.log (200000 / 294057) ∧
    -Real.log (200000 / 294057) ≤ (19272813 / 50000000) := by
  have h := checkLog_sound (w := (94057 / 494057)) (n := 12)
    (lo := (385456259 / 1000000000)) (hi := (19272813 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294057 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294057 / 200000) = 1/(200000 / 294057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (385456259 / 1000000000) (19272813 / 50000000) (Real.log (294057 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (294057 / 200000) = -Real.log (200000 / 294057) := by
    rw [show ((294057 / 200000) : ℝ) = ((200000 / 294057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (79427019 / 125000000) ≤ -Real.log (105943 / 200000) ∧
    -Real.log (105943 / 200000) ≤ (635416153 / 1000000000) := by
  have h := checkLog_sound (w := (94057 / 305943)) (n := 12)
    (lo := (79427019 / 125000000)) (hi := (635416153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 105943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 105943) = 1/(105943 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-635416153 / 1000000000) (-79427019 / 125000000) (Real.log (105943 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38671169 / 100000000) ≤ -Real.log (250000 / 368033) ∧
    -Real.log (250000 / 368033) ≤ (386711691 / 1000000000) := by
  have h := checkLog_sound (w := (118033 / 618033)) (n := 12)
    (lo := (38671169 / 100000000)) (hi := (386711691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368033 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368033 / 250000) = 1/(250000 / 368033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38671169 / 100000000) (386711691 / 1000000000) (Real.log (368033 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (368033 / 250000) = -Real.log (250000 / 368033) := by
    rw [show ((368033 / 250000) : ℝ) = ((250000 / 368033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (319454513 / 500000000) ≤ -Real.log (131967 / 250000) ∧
    -Real.log (131967 / 250000) ≤ (638909027 / 1000000000) := by
  have h := checkLog_sound (w := (118033 / 381967)) (n := 12)
    (lo := (319454513 / 500000000)) (hi := (638909027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 131967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 131967) = 1/(131967 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-638909027 / 1000000000) (-319454513 / 500000000) (Real.log (131967 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1384479723 / 1000000000) ≤ -Real.log (25000000000 / 99818700837) ∧
    -Real.log (25000000000 / 99818700837) ≤ (55379189 / 40000000) := by
  have h := checkLog_sound (w := (49818700837 / 149818700837)) (n := 12)
    (lo := (691332543 / 1000000000)) (hi := (10802071 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99818700837 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(99818700837 / 50000000000) = 1/(25000000000 / 99818700837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1384479723 / 1000000000) (55379189 / 40000000) (Real.log (99818700837 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (99818700837 / 25000000000) = -Real.log (25000000000 / 99818700837) := by
    rw [show ((99818700837 / 25000000000) : ℝ) = ((25000000000 / 99818700837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1390527861 / 1000000000) ≤ -Real.log (100000000000 / 401696990069) ∧
    -Real.log (100000000000 / 401696990069) ≤ (173815983 / 125000000) := by
  have h := checkLog_sound (w := (1696990069 / 801696990069)) (n := 12)
    (lo := (4233501 / 1000000000)) (hi := (2116751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401696990069 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(401696990069 / 400000000000) = 1/(100000000000 / 401696990069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1390527861 / 1000000000) (173815983 / 125000000) (Real.log (401696990069 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (401696990069 / 100000000000) = -Real.log (100000000000 / 401696990069) := by
    rw [show ((401696990069 / 100000000000) : ℝ) = ((100000000000 / 401696990069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1020872411 / 1000000000) ≤ -Real.log (500000000000 / 1387807594649) ∧
    -Real.log (500000000000 / 1387807594649) ≤ (1020872413 / 1000000000) := by
  have h := checkLog_sound (w := (387807594649 / 2387807594649)) (n := 12)
    (lo := (327725231 / 1000000000)) (hi := (20482827 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1387807594649 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1387807594649 / 1000000000000) = 1/(500000000000 / 1387807594649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1020872411 / 1000000000) (1020872413 / 1000000000) (Real.log (1387807594649 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1387807594649 / 500000000000) = -Real.log (500000000000 / 1387807594649) := by
    rw [show ((1387807594649 / 500000000000) : ℝ) = ((500000000000 / 1387807594649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (256405179 / 250000000) ≤ -Real.log (500000000000 / 1394412997189) ∧
    -Real.log (500000000000 / 1394412997189) ≤ (512810359 / 500000000) := by
  have h := checkLog_sound (w := (394412997189 / 2394412997189)) (n := 12)
    (lo := (5194899 / 15625000)) (hi := (332473537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1394412997189 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1394412997189 / 1000000000000) = 1/(500000000000 / 1394412997189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (256405179 / 250000000) (512810359 / 500000000) (Real.log (1394412997189 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1394412997189 / 500000000000) = -Real.log (500000000000 / 1394412997189) := by
    rw [show ((1394412997189 / 500000000000) : ℝ) = ((500000000000 / 1394412997189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0089

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0090Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0090
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

theorem reflection_log_1_neg : (341759573 / 1000000000) ≤ -Real.log (2560 / 3603) ∧
    -Real.log (2560 / 3603) ≤ (170879787 / 500000000) := by
  have h := checkLog_sound (w := (1043 / 6163)) (n := 12)
    (lo := (341759573 / 1000000000)) (hi := (170879787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3603 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3603 / 2560) = 1/(2560 / 3603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341759573 / 1000000000) (170879787 / 500000000) (Real.log (3603 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3603 / 2560) = -Real.log (2560 / 3603) := by
    rw [show ((3603 / 2560) : ℝ) = ((2560 / 3603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (261636279 / 500000000) ≤ -Real.log (1517 / 2560) ∧
    -Real.log (1517 / 2560) ≤ (523272559 / 1000000000) := by
  have h := checkLog_sound (w := (1043 / 4077)) (n := 12)
    (lo := (261636279 / 500000000)) (hi := (523272559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1517) = 1/(1517 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-523272559 / 1000000000) (-261636279 / 500000000) (Real.log (1517 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170463293 / 500000000) ≤ -Real.log (32 / 45) ∧
    -Real.log (32 / 45) ≤ (340926587 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 77)) (n := 12)
    (lo := (170463293 / 500000000)) (hi := (340926587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45 / 32) = 1/(32 / 45) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170463293 / 500000000) (340926587 / 1000000000) (Real.log (45 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (45 / 32) = -Real.log (32 / 45) := by
    rw [show ((45 / 32) : ℝ) = ((32 / 45) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (521296923 / 1000000000) ≤ -Real.log (19 / 32) ∧
    -Real.log (19 / 32) ≤ (130324231 / 250000000) := by
  have h := checkLog_sound (w := (13 / 51)) (n := 12)
    (lo := (521296923 / 1000000000)) (hi := (130324231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 19) = 1/(19 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-130324231 / 250000000) (-521296923 / 1000000000) (Real.log (19 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (953599 / 1600000) ≤ -Real.log (1280 / 2323) ∧
    -Real.log (1280 / 2323) ≤ (37249961 / 62500000) := by
  have h := checkLog_sound (w := (1043 / 3603)) (n := 12)
    (lo := (953599 / 1600000)) (hi := (37249961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2323 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2323 / 1280) = 1/(1280 / 2323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (953599 / 1600000) (37249961 / 62500000) (Real.log (2323 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2323 / 1280) = -Real.log (1280 / 2323) := by
    rw [show ((2323 / 1280) : ℝ) = ((1280 / 2323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (843277607 / 500000000) ≤ -Real.log (237 / 1280) ∧
    -Real.log (237 / 1280) ≤ (1686555217 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 237) = 1/(237 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1686555217 / 1000000000) (-843277607 / 500000000) (Real.log (237 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (594707107 / 1000000000) ≤ -Real.log (16 / 29) ∧
    -Real.log (16 / 29) ≤ (148676777 / 250000000) := by
  have h := checkLog_sound (w := (13 / 45)) (n := 12)
    (lo := (594707107 / 1000000000)) (hi := (148676777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29 / 16) = 1/(16 / 29) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (594707107 / 1000000000) (148676777 / 250000000) (Real.log (29 / 16)) := by
  have h := reflection_log_7_neg
  have he : Real.log (29 / 16) = -Real.log (16 / 29) := by
    rw [show ((29 / 16) : ℝ) = ((16 / 29) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104623527 / 62500000) ≤ -Real.log (3 / 16) ∧
    -Real.log (3 / 16) ≤ (334795287 / 200000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(4 / 3) = 1/(3 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-334795287 / 200000000) (-104623527 / 62500000) (Real.log (3 / 16)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (93686479 / 200000000) ≤ -Real.log (62500 / 99843) ∧
    -Real.log (62500 / 99843) ≤ (117108099 / 250000000) := by
  have h := checkLog_sound (w := (37343 / 162343)) (n := 12)
    (lo := (93686479 / 200000000)) (hi := (117108099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99843 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99843 / 62500) = 1/(62500 / 99843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (93686479 / 200000000) (117108099 / 250000000) (Real.log (99843 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (99843 / 62500) = -Real.log (62500 / 99843) := by
    rw [show ((99843 / 62500) : ℝ) = ((62500 / 99843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (28438449 / 31250000) ≤ -Real.log (25157 / 62500) ∧
    -Real.log (25157 / 62500) ≤ (91003037 / 100000000) := by
  have h := checkLog_sound (w := (6093 / 56407)) (n := 12)
    (lo := (54220797 / 250000000)) (hi := (216883189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 25157) = 1/(25157 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91003037 / 100000000) (-28438449 / 31250000) (Real.log (25157 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (469641063 / 1000000000) ≤ -Real.log (50000 / 79971) ∧
    -Real.log (50000 / 79971) ≤ (58705133 / 125000000) := by
  have h := checkLog_sound (w := (29971 / 129971)) (n := 12)
    (lo := (469641063 / 1000000000)) (hi := (58705133 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79971 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79971 / 50000) = 1/(50000 / 79971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (469641063 / 1000000000) (58705133 / 125000000) (Real.log (79971 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (79971 / 50000) = -Real.log (50000 / 79971) := by
    rw [show ((79971 / 50000) : ℝ) = ((50000 / 79971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (914841781 / 1000000000) ≤ -Real.log (20029 / 50000) ∧
    -Real.log (20029 / 50000) ≤ (914841783 / 1000000000) := by
  have h := checkLog_sound (w := (4971 / 45029)) (n := 12)
    (lo := (221694601 / 1000000000)) (hi := (110847301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 20029) = 1/(20029 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-914841783 / 1000000000) (-914841781 / 1000000000) (Real.log (20029 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (384204017 / 1000000000) ≤ -Real.log (200000 / 293689) ∧
    -Real.log (200000 / 293689) ≤ (192102009 / 500000000) := by
  have h := checkLog_sound (w := (93689 / 493689)) (n := 12)
    (lo := (384204017 / 1000000000)) (hi := (192102009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293689 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293689 / 200000) = 1/(200000 / 293689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (384204017 / 1000000000) (192102009 / 500000000) (Real.log (293689 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (293689 / 200000) = -Real.log (200000 / 293689) := by
    rw [show ((293689 / 200000) : ℝ) = ((200000 / 293689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (126389721 / 200000000) ≤ -Real.log (106311 / 200000) ∧
    -Real.log (106311 / 200000) ≤ (315974303 / 500000000) := by
  have h := checkLog_sound (w := (93689 / 306311)) (n := 12)
    (lo := (126389721 / 200000000)) (hi := (315974303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 106311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 106311) = 1/(106311 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-315974303 / 500000000) (-126389721 / 200000000) (Real.log (106311 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (385456939 / 1000000000) ≤ -Real.log (500000 / 735143) ∧
    -Real.log (500000 / 735143) ≤ (19272847 / 50000000) := by
  have h := checkLog_sound (w := (235143 / 1235143)) (n := 12)
    (lo := (385456939 / 1000000000)) (hi := (19272847 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735143 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735143 / 500000) = 1/(500000 / 735143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (385456939 / 1000000000) (19272847 / 50000000) (Real.log (735143 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (735143 / 500000) = -Real.log (500000 / 735143) := by
    rw [show ((735143 / 500000) : ℝ) = ((500000 / 735143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15885451 / 25000000) ≤ -Real.log (264857 / 500000) ∧
    -Real.log (264857 / 500000) ≤ (635418041 / 1000000000) := by
  have h := checkLog_sound (w := (235143 / 764857)) (n := 12)
    (lo := (15885451 / 25000000)) (hi := (635418041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264857) = 1/(264857 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-635418041 / 1000000000) (-15885451 / 25000000) (Real.log (264857 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1378462763 / 1000000000) ≤ -Real.log (500000000000 / 1984397980681) ∧
    -Real.log (500000000000 / 1984397980681) ≤ (275692553 / 200000000) := by
  have h := checkLog_sound (w := (984397980681 / 2984397980681)) (n := 12)
    (lo := (685315583 / 1000000000)) (hi := (1338507 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1984397980681 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1984397980681 / 1000000000000) = 1/(500000000000 / 1984397980681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1378462763 / 1000000000) (275692553 / 200000000) (Real.log (1984397980681 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1984397980681 / 500000000000) = -Real.log (500000000000 / 1984397980681) := by
    rw [show ((1984397980681 / 500000000000) : ℝ) = ((500000000000 / 1984397980681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (276896569 / 200000000) ≤ -Real.log (1562500000 / 6238688277) ∧
    -Real.log (1562500000 / 6238688277) ≤ (1384482847 / 1000000000) := by
  have h := checkLog_sound (w := (3113688277 / 9363688277)) (n := 12)
    (lo := (138267133 / 200000000)) (hi := (345667833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6238688277 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6238688277 / 3125000000) = 1/(1562500000 / 6238688277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (276896569 / 200000000) (1384482847 / 1000000000) (Real.log (6238688277 / 1562500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6238688277 / 1562500000) = -Real.log (1562500000 / 6238688277) := by
    rw [show ((6238688277 / 1562500000) : ℝ) = ((1562500000 / 6238688277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1016152623 / 1000000000) ≤ -Real.log (500000000000 / 1381272869223) ∧
    -Real.log (500000000000 / 1381272869223) ≤ (8129221 / 8000000) := by
  have h := checkLog_sound (w := (381272869223 / 2381272869223)) (n := 12)
    (lo := (323005443 / 1000000000)) (hi := (80751361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381272869223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1381272869223 / 1000000000000) = 1/(500000000000 / 1381272869223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1016152623 / 1000000000) (8129221 / 8000000) (Real.log (1381272869223 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1381272869223 / 500000000000) = -Real.log (500000000000 / 1381272869223) := by
    rw [show ((1381272869223 / 500000000000) : ℝ) = ((500000000000 / 1381272869223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1020874979 / 1000000000) ≤ -Real.log (20000000000 / 55512446339) ∧
    -Real.log (20000000000 / 55512446339) ≤ (1020874981 / 1000000000) := by
  have h := checkLog_sound (w := (15512446339 / 95512446339)) (n := 12)
    (lo := (327727799 / 1000000000)) (hi := (1638639 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55512446339 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(55512446339 / 40000000000) = 1/(20000000000 / 55512446339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1020874979 / 1000000000) (1020874981 / 1000000000) (Real.log (55512446339 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55512446339 / 20000000000) = -Real.log (20000000000 / 55512446339) := by
    rw [show ((55512446339 / 20000000000) : ℝ) = ((20000000000 / 55512446339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0090

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0091Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0091
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

theorem reflection_log_1_neg : (170463293 / 500000000) ≤ -Real.log (32 / 45) ∧
    -Real.log (32 / 45) ≤ (340926587 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 77)) (n := 12)
    (lo := (170463293 / 500000000)) (hi := (340926587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45 / 32) = 1/(32 / 45) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170463293 / 500000000) (340926587 / 1000000000) (Real.log (45 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (45 / 32) = -Real.log (32 / 45) := by
    rw [show ((45 / 32) : ℝ) = ((32 / 45) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (521296923 / 1000000000) ≤ -Real.log (19 / 32) ∧
    -Real.log (19 / 32) ≤ (130324231 / 250000000) := by
  have h := checkLog_sound (w := (13 / 51)) (n := 12)
    (lo := (521296923 / 1000000000)) (hi := (130324231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 19) = 1/(19 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-130324231 / 250000000) (-521296923 / 1000000000) (Real.log (19 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170046453 / 500000000) ≤ -Real.log (2560 / 3597) ∧
    -Real.log (2560 / 3597) ≤ (340092907 / 1000000000) := by
  have h := checkLog_sound (w := (1037 / 6157)) (n := 12)
    (lo := (170046453 / 500000000)) (hi := (340092907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3597 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3597 / 2560) = 1/(2560 / 3597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170046453 / 500000000) (340092907 / 1000000000) (Real.log (3597 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3597 / 2560) = -Real.log (2560 / 3597) := by
    rw [show ((3597 / 2560) : ℝ) = ((2560 / 3597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1014307 / 1953125) ≤ -Real.log (1523 / 2560) ∧
    -Real.log (1523 / 2560) ≤ (103865037 / 200000000) := by
  have h := checkLog_sound (w := (1037 / 4083)) (n := 12)
    (lo := (1014307 / 1953125)) (hi := (103865037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1523) = 1/(1523 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-103865037 / 200000000) (-1014307 / 1953125) (Real.log (1523 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (594707107 / 1000000000) ≤ -Real.log (16 / 29) ∧
    -Real.log (16 / 29) ≤ (148676777 / 250000000) := by
  have h := checkLog_sound (w := (13 / 45)) (n := 12)
    (lo := (594707107 / 1000000000)) (hi := (148676777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29 / 16) = 1/(16 / 29) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (594707107 / 1000000000) (148676777 / 250000000) (Real.log (29 / 16)) := by
  have h := reflection_log_5_neg
  have he : Real.log (29 / 16) = -Real.log (16 / 29) := by
    rw [show ((29 / 16) : ℝ) = ((16 / 29) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104623527 / 62500000) ≤ -Real.log (3 / 16) ∧
    -Real.log (3 / 16) ≤ (334795287 / 200000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(4 / 3) = 1/(3 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-334795287 / 200000000) (-104623527 / 62500000) (Real.log (3 / 16)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (593413167 / 1000000000) ≤ -Real.log (1280 / 2317) ∧
    -Real.log (1280 / 2317) ≤ (37088323 / 62500000) := by
  have h := checkLog_sound (w := (1037 / 3597)) (n := 12)
    (lo := (593413167 / 1000000000)) (hi := (37088323 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2317 / 1280) = 1/(1280 / 2317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (593413167 / 1000000000) (37088323 / 62500000) (Real.log (2317 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2317 / 1280) = -Real.log (1280 / 2317) := by
    rw [show ((2317 / 1280) : ℝ) = ((1280 / 2317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (207694239 / 125000000) ≤ -Real.log (243 / 1280) ∧
    -Real.log (243 / 1280) ≤ (332310783 / 200000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 243) = 1/(243 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-332310783 / 200000000) (-207694239 / 125000000) (Real.log (243 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (233612699 / 500000000) ≤ -Real.log (1000000 / 1595561) ∧
    -Real.log (1000000 / 1595561) ≤ (467225399 / 1000000000) := by
  have h := checkLog_sound (w := (595561 / 2595561)) (n := 12)
    (lo := (233612699 / 500000000)) (hi := (467225399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1595561 / 1000000) = 1/(1000000 / 1595561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (233612699 / 500000000) (467225399 / 1000000000) (Real.log (1595561 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1595561 / 1000000) = -Real.log (1000000 / 1595561) := by
    rw [show ((1595561 / 1000000) : ℝ) = ((1000000 / 1595561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (226313589 / 250000000) ≤ -Real.log (404439 / 1000000) ∧
    -Real.log (404439 / 1000000) ≤ (452627179 / 500000000) := by
  have h := checkLog_sound (w := (95561 / 904439)) (n := 12)
    (lo := (26513397 / 125000000)) (hi := (212107177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 404439) = 1/(404439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-452627179 / 500000000) (-226313589 / 250000000) (Real.log (404439 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (468433021 / 1000000000) ≤ -Real.log (1000000 / 1597489) ∧
    -Real.log (1000000 / 1597489) ≤ (234216511 / 500000000) := by
  have h := checkLog_sound (w := (597489 / 2597489)) (n := 12)
    (lo := (468433021 / 1000000000)) (hi := (234216511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1597489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1597489 / 1000000) = 1/(1000000 / 1597489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (468433021 / 1000000000) (234216511 / 500000000) (Real.log (1597489 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1597489 / 1000000) = -Real.log (1000000 / 1597489) := by
    rw [show ((1597489 / 1000000) : ℝ) = ((1000000 / 1597489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (227508213 / 250000000) ≤ -Real.log (402511 / 1000000) ∧
    -Real.log (402511 / 1000000) ≤ (455016427 / 500000000) := by
  have h := checkLog_sound (w := (97489 / 902511)) (n := 12)
    (lo := (27110709 / 125000000)) (hi := (216885673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 402511) = 1/(402511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-455016427 / 500000000) (-227508213 / 250000000) (Real.log (402511 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (191477489 / 500000000) ≤ -Real.log (250000 / 366653) ∧
    -Real.log (250000 / 366653) ≤ (382954979 / 1000000000) := by
  have h := checkLog_sound (w := (116653 / 616653)) (n := 12)
    (lo := (191477489 / 500000000)) (hi := (382954979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366653 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366653 / 250000) = 1/(250000 / 366653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (191477489 / 500000000) (382954979 / 1000000000) (Real.log (366653 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (366653 / 250000) = -Real.log (250000 / 366653) := by
    rw [show ((366653 / 250000) : ℝ) = ((250000 / 366653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (157126541 / 250000000) ≤ -Real.log (133347 / 250000) ∧
    -Real.log (133347 / 250000) ≤ (125701233 / 200000000) := by
  have h := checkLog_sound (w := (116653 / 383347)) (n := 12)
    (lo := (157126541 / 250000000)) (hi := (125701233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 133347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 133347) = 1/(133347 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-125701233 / 200000000) (-157126541 / 250000000) (Real.log (133347 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (192102349 / 500000000) ≤ -Real.log (500000 / 734223) ∧
    -Real.log (500000 / 734223) ≤ (384204699 / 1000000000) := by
  have h := checkLog_sound (w := (234223 / 1234223)) (n := 12)
    (lo := (192102349 / 500000000)) (hi := (384204699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734223 / 500000) = 1/(500000 / 734223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192102349 / 500000000) (384204699 / 1000000000) (Real.log (734223 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (734223 / 500000) = -Real.log (500000 / 734223) := by
    rw [show ((734223 / 500000) : ℝ) = ((500000 / 734223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (631950487 / 1000000000) ≤ -Real.log (265777 / 500000) ∧
    -Real.log (265777 / 500000) ≤ (78993811 / 125000000) := by
  have h := checkLog_sound (w := (234223 / 765777)) (n := 12)
    (lo := (631950487 / 1000000000)) (hi := (78993811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 265777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 265777) = 1/(265777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78993811 / 125000000) (-631950487 / 1000000000) (Real.log (265777 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (274495951 / 200000000) ≤ -Real.log (500000000000 / 1972560756999) ∧
    -Real.log (500000000000 / 1972560756999) ≤ (1372479757 / 1000000000) := by
  have h := checkLog_sound (w := (972560756999 / 2972560756999)) (n := 12)
    (lo := (27173303 / 40000000)) (hi := (21229143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972560756999 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1972560756999 / 1000000000000) = 1/(500000000000 / 1972560756999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (274495951 / 200000000) (1372479757 / 1000000000) (Real.log (1972560756999 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1972560756999 / 500000000000) = -Real.log (500000000000 / 1972560756999) := by
    rw [show ((1972560756999 / 500000000000) : ℝ) = ((500000000000 / 1972560756999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (689232937 / 500000000) ≤ -Real.log (50000000000 / 198440415293) ∧
    -Real.log (50000000000 / 198440415293) ≤ (344616469 / 250000000) := by
  have h := checkLog_sound (w := (98440415293 / 298440415293)) (n := 12)
    (lo := (342659347 / 500000000)) (hi := (137063739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198440415293 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(198440415293 / 100000000000) = 1/(50000000000 / 198440415293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (689232937 / 500000000) (344616469 / 250000000) (Real.log (198440415293 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (198440415293 / 50000000000) = -Real.log (50000000000 / 198440415293) := by
    rw [show ((198440415293 / 50000000000) : ℝ) = ((50000000000 / 198440415293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (505730571 / 500000000) ≤ -Real.log (500000000000 / 1374807832197) ∧
    -Real.log (500000000000 / 1374807832197) ≤ (126432643 / 125000000) := by
  have h := checkLog_sound (w := (374807832197 / 2374807832197)) (n := 12)
    (lo := (159156981 / 500000000)) (hi := (318313963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374807832197 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1374807832197 / 1000000000000) = 1/(500000000000 / 1374807832197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (505730571 / 500000000) (126432643 / 125000000) (Real.log (1374807832197 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1374807832197 / 500000000000) = -Real.log (500000000000 / 1374807832197) := by
    rw [show ((1374807832197 / 500000000000) : ℝ) = ((500000000000 / 1374807832197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (203231037 / 200000000) ≤ -Real.log (250000000000 / 690638204209) ∧
    -Real.log (250000000000 / 690638204209) ≤ (1016155187 / 1000000000) := by
  have h := checkLog_sound (w := (190638204209 / 1190638204209)) (n := 12)
    (lo := (64601601 / 200000000)) (hi := (161504003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690638204209 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(690638204209 / 500000000000) = 1/(250000000000 / 690638204209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (203231037 / 200000000) (1016155187 / 1000000000) (Real.log (690638204209 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (690638204209 / 250000000000) = -Real.log (250000000000 / 690638204209) := by
    rw [show ((690638204209 / 250000000000) : ℝ) = ((250000000000 / 690638204209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0091

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0092Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0092
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

theorem reflection_log_1_neg : (170046453 / 500000000) ≤ -Real.log (2560 / 3597) ∧
    -Real.log (2560 / 3597) ≤ (340092907 / 1000000000) := by
  have h := checkLog_sound (w := (1037 / 6157)) (n := 12)
    (lo := (170046453 / 500000000)) (hi := (340092907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3597 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3597 / 2560) = 1/(2560 / 3597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170046453 / 500000000) (340092907 / 1000000000) (Real.log (3597 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3597 / 2560) = -Real.log (2560 / 3597) := by
    rw [show ((3597 / 2560) : ℝ) = ((2560 / 3597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1014307 / 1953125) ≤ -Real.log (1523 / 2560) ∧
    -Real.log (1523 / 2560) ≤ (103865037 / 200000000) := by
  have h := checkLog_sound (w := (1037 / 4083)) (n := 12)
    (lo := (1014307 / 1953125)) (hi := (103865037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1523) = 1/(1523 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-103865037 / 200000000) (-1014307 / 1953125) (Real.log (1523 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (339258529 / 1000000000) ≤ -Real.log (1280 / 1797) ∧
    -Real.log (1280 / 1797) ≤ (33925853 / 100000000) := by
  have h := checkLog_sound (w := (517 / 3077)) (n := 12)
    (lo := (339258529 / 1000000000)) (hi := (33925853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1797 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1797 / 1280) = 1/(1280 / 1797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (339258529 / 1000000000) (33925853 / 100000000) (Real.log (1797 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1797 / 1280) = -Real.log (1280 / 1797) := by
    rw [show ((1797 / 1280) : ℝ) = ((1280 / 1797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20694293 / 40000000) ≤ -Real.log (763 / 1280) ∧
    -Real.log (763 / 1280) ≤ (258678663 / 500000000) := by
  have h := checkLog_sound (w := (517 / 2043)) (n := 12)
    (lo := (20694293 / 40000000)) (hi := (258678663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 763) = 1/(763 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-258678663 / 500000000) (-20694293 / 40000000) (Real.log (763 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (593413167 / 1000000000) ≤ -Real.log (1280 / 2317) ∧
    -Real.log (1280 / 2317) ≤ (37088323 / 62500000) := by
  have h := checkLog_sound (w := (1037 / 3597)) (n := 12)
    (lo := (593413167 / 1000000000)) (hi := (37088323 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2317 / 1280) = 1/(1280 / 2317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (593413167 / 1000000000) (37088323 / 62500000) (Real.log (2317 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2317 / 1280) = -Real.log (1280 / 2317) := by
    rw [show ((2317 / 1280) : ℝ) = ((1280 / 2317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (207694239 / 125000000) ≤ -Real.log (243 / 1280) ∧
    -Real.log (243 / 1280) ≤ (332310783 / 200000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 243) = 1/(243 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-332310783 / 200000000) (-207694239 / 125000000) (Real.log (243 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18640753 / 40000000) ≤ -Real.log (1000000 / 1593637) ∧
    -Real.log (1000000 / 1593637) ≤ (233009413 / 500000000) := by
  have h := checkLog_sound (w := (593637 / 2593637)) (n := 12)
    (lo := (18640753 / 40000000)) (hi := (233009413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593637 / 1000000) = 1/(1000000 / 1593637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18640753 / 40000000) (233009413 / 500000000) (Real.log (1593637 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1593637 / 1000000) = -Real.log (1000000 / 1593637) := by
    rw [show ((1593637 / 1000000) : ℝ) = ((1000000 / 1593637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (900508429 / 1000000000) ≤ -Real.log (406363 / 1000000) ∧
    -Real.log (406363 / 1000000) ≤ (900508431 / 1000000000) := by
  have h := checkLog_sound (w := (93637 / 906363)) (n := 12)
    (lo := (207361249 / 1000000000)) (hi := (165889 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 406363) = 1/(406363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-900508431 / 1000000000) (-900508429 / 1000000000) (Real.log (406363 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18689041 / 40000000) ≤ -Real.log (500000 / 797781) ∧
    -Real.log (500000 / 797781) ≤ (233613013 / 500000000) := by
  have h := checkLog_sound (w := (297781 / 1297781)) (n := 12)
    (lo := (18689041 / 40000000)) (hi := (233613013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797781 / 500000) = 1/(500000 / 797781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18689041 / 40000000) (233613013 / 500000000) (Real.log (797781 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (797781 / 500000) = -Real.log (500000 / 797781) := by
    rw [show ((797781 / 500000) : ℝ) = ((500000 / 797781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (905256829 / 1000000000) ≤ -Real.log (202219 / 500000) ∧
    -Real.log (202219 / 500000) ≤ (905256831 / 1000000000) := by
  have h := checkLog_sound (w := (47781 / 452219)) (n := 12)
    (lo := (212109649 / 1000000000)) (hi := (4242193 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 202219) = 1/(202219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-905256831 / 1000000000) (-905256829 / 1000000000) (Real.log (202219 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190854237 / 500000000) ≤ -Real.log (200000 / 292957) ∧
    -Real.log (200000 / 292957) ≤ (15268339 / 40000000) := by
  have h := checkLog_sound (w := (92957 / 492957)) (n := 12)
    (lo := (190854237 / 500000000)) (hi := (15268339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292957 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292957 / 200000) = 1/(200000 / 292957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190854237 / 500000000) (15268339 / 40000000) (Real.log (292957 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (292957 / 200000) = -Real.log (200000 / 292957) := by
    rw [show ((292957 / 200000) : ℝ) = ((200000 / 292957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (625086743 / 1000000000) ≤ -Real.log (107043 / 200000) ∧
    -Real.log (107043 / 200000) ≤ (78135843 / 125000000) := by
  have h := checkLog_sound (w := (92957 / 307043)) (n := 12)
    (lo := (625086743 / 1000000000)) (hi := (78135843 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 107043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 107043) = 1/(107043 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78135843 / 125000000) (-625086743 / 1000000000) (Real.log (107043 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19147783 / 50000000) ≤ -Real.log (1000000 / 1466613) ∧
    -Real.log (1000000 / 1466613) ≤ (382955661 / 1000000000) := by
  have h := checkLog_sound (w := (466613 / 2466613)) (n := 12)
    (lo := (19147783 / 50000000)) (hi := (382955661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1466613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1466613 / 1000000) = 1/(1000000 / 1466613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19147783 / 50000000) (382955661 / 1000000000) (Real.log (1466613 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1466613 / 1000000) = -Real.log (1000000 / 1466613) := by
    rw [show ((1466613 / 1000000) : ℝ) = ((1000000 / 1466613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (628508039 / 1000000000) ≤ -Real.log (533387 / 1000000) ∧
    -Real.log (533387 / 1000000) ≤ (15712701 / 25000000) := by
  have h := checkLog_sound (w := (466613 / 1533387)) (n := 12)
    (lo := (628508039 / 1000000000)) (hi := (15712701 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 533387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 533387) = 1/(533387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15712701 / 25000000) (-628508039 / 1000000000) (Real.log (533387 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (273305451 / 200000000) ≤ -Real.log (500000000000 / 1960853965543) ∧
    -Real.log (500000000000 / 1960853965543) ≤ (1366527257 / 1000000000) := by
  have h := checkLog_sound (w := (960853965543 / 2960853965543)) (n := 12)
    (lo := (26935203 / 40000000)) (hi := (168345019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960853965543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1960853965543 / 1000000000000) = 1/(500000000000 / 1960853965543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (273305451 / 200000000) (1366527257 / 1000000000) (Real.log (1960853965543 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1960853965543 / 500000000000) = -Real.log (500000000000 / 1960853965543) := by
    rw [show ((1960853965543 / 500000000000) : ℝ) = ((500000000000 / 1960853965543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (686241427 / 500000000) ≤ -Real.log (125000000000 / 493141717643) ∧
    -Real.log (125000000000 / 493141717643) ≤ (171560357 / 125000000) := by
  have h := checkLog_sound (w := (243141717643 / 743141717643)) (n := 12)
    (lo := (339667837 / 500000000)) (hi := (27173427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493141717643 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(493141717643 / 250000000000) = 1/(125000000000 / 493141717643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (686241427 / 500000000) (171560357 / 125000000) (Real.log (493141717643 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (493141717643 / 125000000000) = -Real.log (125000000000 / 493141717643) := by
    rw [show ((493141717643 / 125000000000) : ℝ) = ((125000000000 / 493141717643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1006795217 / 1000000000) ≤ -Real.log (15625000000 / 42762750717) ∧
    -Real.log (15625000000 / 42762750717) ≤ (1006795219 / 1000000000) := by
  have h := checkLog_sound (w := (11512750717 / 74012750717)) (n := 12)
    (lo := (313648037 / 1000000000)) (hi := (156824019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42762750717 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42762750717 / 31250000000) = 1/(15625000000 / 42762750717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1006795217 / 1000000000) (1006795219 / 1000000000) (Real.log (42762750717 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (42762750717 / 15625000000) = -Real.log (15625000000 / 42762750717) := by
    rw [show ((42762750717 / 15625000000) : ℝ) = ((15625000000 / 42762750717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1011463699 / 1000000000) ≤ -Real.log (500000000000 / 1374811347109) ∧
    -Real.log (500000000000 / 1374811347109) ≤ (1011463701 / 1000000000) := by
  have h := checkLog_sound (w := (374811347109 / 2374811347109)) (n := 12)
    (lo := (318316519 / 1000000000)) (hi := (7957913 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374811347109 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1374811347109 / 1000000000000) = 1/(500000000000 / 1374811347109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1011463699 / 1000000000) (1011463701 / 1000000000) (Real.log (1374811347109 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1374811347109 / 500000000000) = -Real.log (500000000000 / 1374811347109) := by
    rw [show ((1374811347109 / 500000000000) : ℝ) = ((500000000000 / 1374811347109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0092

end


