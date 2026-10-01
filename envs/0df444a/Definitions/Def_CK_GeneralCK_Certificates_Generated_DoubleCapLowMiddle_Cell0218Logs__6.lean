-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0218Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0218Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:57:32.453379+00:00
-- url     : https://prove2.me/theorems/f7cb01e0-9a46-4de3-a117-5613a318a2d5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0218Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0219Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0218Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0219Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0220Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0221Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0222Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0223Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0218Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0219Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0220Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0221Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0222Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0223Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0218Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0219Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0220Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0221Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0222Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0223Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0218Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0219Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0220Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0221Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0222Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0223Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0218Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0218
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

theorem reflection_log_1_neg : (531179569 / 1000000000) ≤ -Real.log (3200 / 5443) ∧
    -Real.log (3200 / 5443) ≤ (53117957 / 100000000) := by
  have h := checkLog_sound (w := (2243 / 8643)) (n := 12)
    (lo := (531179569 / 1000000000)) (hi := (53117957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5443 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5443 / 3200) = 1/(3200 / 5443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (531179569 / 1000000000) (53117957 / 100000000) (Real.log (5443 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5443 / 3200) = -Real.log (3200 / 5443) := by
    rw [show ((5443 / 3200) : ℝ) = ((3200 / 5443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (150887837 / 125000000) ≤ -Real.log (957 / 3200) ∧
    -Real.log (957 / 3200) ≤ (603551349 / 500000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 957) = 1/(957 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-603551349 / 500000000) (-150887837 / 125000000) (Real.log (957 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26384137 / 50000000) ≤ -Real.log (200 / 339) ∧
    -Real.log (200 / 339) ≤ (527682741 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 539)) (n := 12)
    (lo := (26384137 / 50000000)) (hi := (527682741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 200) = 1/(200 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26384137 / 50000000) (527682741 / 1000000000) (Real.log (339 / 200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (339 / 200) = -Real.log (200 / 339) := by
    rw [show ((339 / 200) : ℝ) = ((200 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1187443501 / 1000000000) ≤ -Real.log (61 / 200) ∧
    -Real.log (61 / 200) ≤ (1187443503 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 61) = 1/(61 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1187443503 / 1000000000) (-1187443501 / 1000000000) (Real.log (61 / 200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168905313 / 500000000) ≤ -Real.log (1600 / 2243) ∧
    -Real.log (1600 / 2243) ≤ (337810627 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 3843)) (n := 12)
    (lo := (168905313 / 500000000)) (hi := (337810627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2243 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2243 / 1600) = 1/(1600 / 2243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168905313 / 500000000) (337810627 / 1000000000) (Real.log (2243 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2243 / 1600) = -Real.log (1600 / 2243) := by
    rw [show ((2243 / 1600) : ℝ) = ((1600 / 2243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (128488879 / 250000000) ≤ -Real.log (957 / 1600) ∧
    -Real.log (957 / 1600) ≤ (513955517 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 957) = 1/(957 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-513955517 / 1000000000) (-128488879 / 250000000) (Real.log (957 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (329303747 / 1000000000) ≤ -Real.log (100 / 139) ∧
    -Real.log (100 / 139) ≤ (82325937 / 250000000) := by
  have h := checkLog_sound (w := (39 / 239)) (n := 12)
    (lo := (329303747 / 1000000000)) (hi := (82325937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 100) = 1/(100 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (329303747 / 1000000000) (82325937 / 250000000) (Real.log (139 / 100)) := by
  have h := reflection_log_7_neg
  have he : Real.log (139 / 100) = -Real.log (100 / 139) := by
    rw [show ((139 / 100) : ℝ) = ((100 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (494296321 / 1000000000) ≤ -Real.log (61 / 100) ∧
    -Real.log (61 / 100) ≤ (247148161 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 61) = 1/(61 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-247148161 / 500000000) (-494296321 / 1000000000) (Real.log (61 / 100)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (596452893 / 1000000000) ≤ -Real.log (1000000 / 1815667) ∧
    -Real.log (1000000 / 1815667) ≤ (298226447 / 500000000) := by
  have h := checkLog_sound (w := (815667 / 2815667)) (n := 12)
    (lo := (596452893 / 1000000000)) (hi := (298226447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1815667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1815667 / 1000000) = 1/(1000000 / 1815667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (596452893 / 1000000000) (298226447 / 500000000) (Real.log (1815667 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1815667 / 1000000) = -Real.log (1000000 / 1815667) := by
    rw [show ((1815667 / 1000000) : ℝ) = ((1000000 / 1815667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1691011373 / 1000000000) ≤ -Real.log (184333 / 1000000) ∧
    -Real.log (184333 / 1000000) ≤ (105688211 / 62500000) := by
  have h := checkLog_sound (w := (65667 / 434333)) (n := 12)
    (lo := (304717013 / 1000000000)) (hi := (152358507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184333) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 184333) = 1/(184333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-105688211 / 62500000) (-1691011373 / 1000000000) (Real.log (184333 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149411833 / 250000000) ≤ -Real.log (1000000 / 1817837) ∧
    -Real.log (1000000 / 1817837) ≤ (597647333 / 1000000000) := by
  have h := checkLog_sound (w := (817837 / 2817837)) (n := 12)
    (lo := (149411833 / 250000000)) (hi := (597647333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1817837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1817837 / 1000000) = 1/(1000000 / 1817837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149411833 / 250000000) (597647333 / 1000000000) (Real.log (1817837 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1817837 / 1000000) = -Real.log (1000000 / 1817837) := by
    rw [show ((1817837 / 1000000) : ℝ) = ((1000000 / 1817837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1702853387 / 1000000000) ≤ -Real.log (182163 / 1000000) ∧
    -Real.log (182163 / 1000000) ≤ (170285339 / 100000000) := by
  have h := checkLog_sound (w := (67837 / 432163)) (n := 12)
    (lo := (316559027 / 1000000000)) (hi := (79139757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182163) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 182163) = 1/(182163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-170285339 / 100000000) (-1702853387 / 1000000000) (Real.log (182163 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (288567569 / 500000000) ≤ -Real.log (1000000 / 1780929) ∧
    -Real.log (1000000 / 1780929) ≤ (577135139 / 1000000000) := by
  have h := checkLog_sound (w := (780929 / 2780929)) (n := 12)
    (lo := (288567569 / 500000000)) (hi := (577135139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780929 / 1000000) = 1/(1000000 / 1780929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (288567569 / 500000000) (577135139 / 1000000000) (Real.log (1780929 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1780929 / 1000000) = -Real.log (1000000 / 1780929) := by
    rw [show ((1780929 / 1000000) : ℝ) = ((1000000 / 1780929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1518359399 / 1000000000) ≤ -Real.log (219071 / 1000000) ∧
    -Real.log (219071 / 1000000) ≤ (759179701 / 500000000) := by
  have h := checkLog_sound (w := (30929 / 469071)) (n := 12)
    (lo := (132065039 / 1000000000)) (hi := (1650813 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219071) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219071) = 1/(219071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-759179701 / 500000000) (-1518359399 / 1000000000) (Real.log (219071 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (9051303 / 15625000) ≤ -Real.log (1000000 / 1784759) ∧
    -Real.log (1000000 / 1784759) ≤ (579283393 / 1000000000) := by
  have h := checkLog_sound (w := (784759 / 2784759)) (n := 12)
    (lo := (9051303 / 15625000)) (hi := (579283393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1784759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1784759 / 1000000) = 1/(1000000 / 1784759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9051303 / 15625000) (579283393 / 1000000000) (Real.log (1784759 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1784759 / 1000000) = -Real.log (1000000 / 1784759) := by
    rw [show ((1784759 / 1000000) : ℝ) = ((1000000 / 1784759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1535996947 / 1000000000) ≤ -Real.log (215241 / 1000000) ∧
    -Real.log (215241 / 1000000) ≤ (30719939 / 20000000) := by
  have h := checkLog_sound (w := (34759 / 465241)) (n := 12)
    (lo := (149702587 / 1000000000)) (hi := (37425647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215241) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 215241) = 1/(215241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-30719939 / 20000000) (-1535996947 / 1000000000) (Real.log (215241 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1143732133 / 500000000) ≤ -Real.log (100000000000 / 984992920421) ∧
    -Real.log (100000000000 / 984992920421) ≤ (228746427 / 100000000) := by
  have h := checkLog_sound (w := (184992920421 / 1784992920421)) (n := 12)
    (lo := (104011363 / 500000000)) (hi := (208022727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((984992920421 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(984992920421 / 800000000000) = 1/(100000000000 / 984992920421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1143732133 / 500000000) (228746427 / 100000000) (Real.log (984992920421 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (984992920421 / 100000000000) = -Real.log (100000000000 / 984992920421) := by
    rw [show ((984992920421 / 100000000000) : ℝ) = ((100000000000 / 984992920421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2300500719 / 1000000000) ≤ -Real.log (62500000000 / 623698624309) ∧
    -Real.log (62500000000 / 623698624309) ≤ (2300500723 / 1000000000) := by
  have h := checkLog_sound (w := (123698624309 / 1123698624309)) (n := 12)
    (lo := (221059179 / 1000000000)) (hi := (11052959 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623698624309 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(623698624309 / 500000000000) = 1/(62500000000 / 623698624309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2300500719 / 1000000000) (2300500723 / 1000000000) (Real.log (623698624309 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (623698624309 / 62500000000) = -Real.log (62500000000 / 623698624309) := by
    rw [show ((623698624309 / 62500000000) : ℝ) = ((62500000000 / 623698624309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2095494537 / 1000000000) ≤ -Real.log (62500000000 / 508091269497) ∧
    -Real.log (62500000000 / 508091269497) ≤ (2095494541 / 1000000000) := by
  have h := checkLog_sound (w := (8091269497 / 1008091269497)) (n := 12)
    (lo := (16052997 / 1000000000)) (hi := (8026499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508091269497 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(508091269497 / 500000000000) = 1/(62500000000 / 508091269497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2095494537 / 1000000000) (2095494541 / 1000000000) (Real.log (508091269497 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (508091269497 / 62500000000) = -Real.log (62500000000 / 508091269497) := by
    rw [show ((508091269497 / 62500000000) : ℝ) = ((62500000000 / 508091269497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1057640169 / 500000000) ≤ -Real.log (6250000000 / 51824437491) ∧
    -Real.log (6250000000 / 51824437491) ≤ (1057640171 / 500000000) := by
  have h := checkLog_sound (w := (1824437491 / 101824437491)) (n := 12)
    (lo := (17919399 / 500000000)) (hi := (35838799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51824437491 / 50000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(51824437491 / 50000000000) = 1/(6250000000 / 51824437491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1057640169 / 500000000) (1057640171 / 500000000) (Real.log (51824437491 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (51824437491 / 6250000000) = -Real.log (6250000000 / 51824437491) := by
    rw [show ((51824437491 / 6250000000) : ℝ) = ((6250000000 / 51824437491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0218

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0219Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0219
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

theorem reflection_log_1_neg : (26384137 / 50000000) ≤ -Real.log (200 / 339) ∧
    -Real.log (200 / 339) ≤ (527682741 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 539)) (n := 12)
    (lo := (26384137 / 50000000)) (hi := (527682741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 200) = 1/(200 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26384137 / 50000000) (527682741 / 1000000000) (Real.log (339 / 200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (339 / 200) = -Real.log (200 / 339) := by
    rw [show ((339 / 200) : ℝ) = ((200 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1187443501 / 1000000000) ≤ -Real.log (61 / 200) ∧
    -Real.log (61 / 200) ≤ (1187443503 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 61) = 1/(61 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1187443503 / 1000000000) (-1187443501 / 1000000000) (Real.log (61 / 200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (524173641 / 1000000000) ≤ -Real.log (640 / 1081) ∧
    -Real.log (640 / 1081) ≤ (262086821 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1721)) (n := 12)
    (lo := (524173641 / 1000000000)) (hi := (262086821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081 / 640) = 1/(640 / 1081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (524173641 / 1000000000) (262086821 / 500000000) (Real.log (1081 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1081 / 640) = -Real.log (640 / 1081) := by
    rw [show ((1081 / 640) : ℝ) = ((640 / 1081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1168163351 / 1000000000) ≤ -Real.log (199 / 640) ∧
    -Real.log (199 / 640) ≤ (1168163353 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 199) = 1/(199 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1168163353 / 1000000000) (-1168163351 / 1000000000) (Real.log (199 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (329303747 / 1000000000) ≤ -Real.log (100 / 139) ∧
    -Real.log (100 / 139) ≤ (82325937 / 250000000) := by
  have h := checkLog_sound (w := (39 / 239)) (n := 12)
    (lo := (329303747 / 1000000000)) (hi := (82325937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 100) = 1/(100 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (329303747 / 1000000000) (82325937 / 250000000) (Real.log (139 / 100)) := by
  have h := reflection_log_5_neg
  have he : Real.log (139 / 100) = -Real.log (100 / 139) := by
    rw [show ((139 / 100) : ℝ) = ((100 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (494296321 / 1000000000) ≤ -Real.log (61 / 100) ∧
    -Real.log (61 / 100) ≤ (247148161 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 61) = 1/(61 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247148161 / 500000000) (-494296321 / 1000000000) (Real.log (61 / 100)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148822941 / 250000000) ≤ -Real.log (25000 / 45339) ∧
    -Real.log (25000 / 45339) ≤ (119058353 / 200000000) := by
  have h := checkLog_sound (w := (20339 / 70339)) (n := 12)
    (lo := (148822941 / 250000000)) (hi := (119058353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45339 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45339 / 25000) = 1/(25000 / 45339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148822941 / 250000000) (119058353 / 200000000) (Real.log (45339 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (45339 / 25000) = -Real.log (25000 / 45339) := by
    rw [show ((45339 / 25000) : ℝ) = ((25000 / 45339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (839822903 / 500000000) ≤ -Real.log (4661 / 25000) ∧
    -Real.log (4661 / 25000) ≤ (1679645809 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 10911)) (n := 12)
    (lo := (146675723 / 500000000)) (hi := (293351447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4661) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6250 / 4661) = 1/(4661 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1679645809 / 1000000000) (-839822903 / 500000000) (Real.log (4661 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (298226997 / 500000000) ≤ -Real.log (1000000 / 1815669) ∧
    -Real.log (1000000 / 1815669) ≤ (119290799 / 200000000) := by
  have h := checkLog_sound (w := (815669 / 2815669)) (n := 12)
    (lo := (298226997 / 500000000)) (hi := (119290799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1815669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1815669 / 1000000) = 1/(1000000 / 1815669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (298226997 / 500000000) (119290799 / 200000000) (Real.log (1815669 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1815669 / 1000000) = -Real.log (1000000 / 1815669) := by
    rw [show ((1815669 / 1000000) : ℝ) = ((1000000 / 1815669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1691022223 / 1000000000) ≤ -Real.log (184331 / 1000000) ∧
    -Real.log (184331 / 1000000) ≤ (845511113 / 500000000) := by
  have h := checkLog_sound (w := (65669 / 434331)) (n := 12)
    (lo := (304727863 / 1000000000)) (hi := (38090983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184331) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 184331) = 1/(184331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-845511113 / 500000000) (-1691022223 / 1000000000) (Real.log (184331 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (287493943 / 500000000) ≤ -Real.log (1000000 / 1777109) ∧
    -Real.log (1000000 / 1777109) ≤ (574987887 / 1000000000) := by
  have h := checkLog_sound (w := (777109 / 2777109)) (n := 12)
    (lo := (287493943 / 500000000)) (hi := (574987887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777109 / 1000000) = 1/(1000000 / 1777109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (287493943 / 500000000) (574987887 / 1000000000) (Real.log (1777109 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1777109 / 1000000) = -Real.log (1000000 / 1777109) := by
    rw [show ((1777109 / 1000000) : ℝ) = ((1000000 / 1777109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (300214483 / 200000000) ≤ -Real.log (222891 / 1000000) ∧
    -Real.log (222891 / 1000000) ≤ (750536209 / 500000000) := by
  have h := checkLog_sound (w := (27109 / 472891)) (n := 12)
    (lo := (22955611 / 200000000)) (hi := (14347257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222891) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 222891) = 1/(222891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-750536209 / 500000000) (-300214483 / 200000000) (Real.log (222891 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (577135699 / 1000000000) ≤ -Real.log (100000 / 178093) ∧
    -Real.log (100000 / 178093) ≤ (5771357 / 10000000) := by
  have h := checkLog_sound (w := (78093 / 278093)) (n := 12)
    (lo := (577135699 / 1000000000)) (hi := (5771357 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178093 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178093 / 100000) = 1/(100000 / 178093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (577135699 / 1000000000) (5771357 / 10000000) (Real.log (178093 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (178093 / 100000) = -Real.log (100000 / 178093) := by
    rw [show ((178093 / 100000) : ℝ) = ((100000 / 178093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (379590991 / 250000000) ≤ -Real.log (21907 / 100000) ∧
    -Real.log (21907 / 100000) ≤ (1518363967 / 1000000000) := by
  have h := checkLog_sound (w := (3093 / 46907)) (n := 12)
    (lo := (33017401 / 250000000)) (hi := (26413921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 21907) = 1/(21907 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1518363967 / 1000000000) (-379590991 / 250000000) (Real.log (21907 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (227493757 / 100000000) ≤ -Real.log (500000000000 / 4863655867839) ∧
    -Real.log (500000000000 / 4863655867839) ≤ (1137468787 / 500000000) := by
  have h := checkLog_sound (w := (863655867839 / 8863655867839)) (n := 12)
    (lo := (19549603 / 100000000)) (hi := (195496031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4863655867839 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4863655867839 / 4000000000000) = 1/(500000000000 / 4863655867839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (227493757 / 100000000) (1137468787 / 500000000) (Real.log (4863655867839 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4863655867839 / 500000000000) = -Real.log (500000000000 / 4863655867839) := by
    rw [show ((4863655867839 / 500000000000) : ℝ) = ((500000000000 / 4863655867839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2287476217 / 1000000000) ≤ -Real.log (500000000000 / 4925023463227) ∧
    -Real.log (500000000000 / 4925023463227) ≤ (2287476221 / 1000000000) := by
  have h := checkLog_sound (w := (925023463227 / 8925023463227)) (n := 12)
    (lo := (208034677 / 1000000000)) (hi := (104017339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4925023463227 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4925023463227 / 4000000000000) = 1/(500000000000 / 4925023463227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2287476217 / 1000000000) (2287476221 / 1000000000) (Real.log (4925023463227 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4925023463227 / 500000000000) = -Real.log (500000000000 / 4925023463227) := by
    rw [show ((4925023463227 / 500000000000) : ℝ) = ((500000000000 / 4925023463227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2076060301 / 1000000000) ≤ -Real.log (62500000000 / 498312235577) ∧
    -Real.log (62500000000 / 498312235577) ≤ (129753769 / 62500000) := by
  have h := checkLog_sound (w := (248312235577 / 748312235577)) (n := 12)
    (lo := (689765941 / 1000000000)) (hi := (344882971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((498312235577 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(498312235577 / 250000000000) = 1/(62500000000 / 498312235577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2076060301 / 1000000000) (129753769 / 62500000) (Real.log (498312235577 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (498312235577 / 62500000000) = -Real.log (62500000000 / 498312235577) := by
    rw [show ((498312235577 / 62500000000) : ℝ) = ((62500000000 / 498312235577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2095499663 / 1000000000) ≤ -Real.log (250000000000 / 2032375496417) ∧
    -Real.log (250000000000 / 2032375496417) ≤ (2095499667 / 1000000000) := by
  have h := checkLog_sound (w := (32375496417 / 4032375496417)) (n := 12)
    (lo := (16058123 / 1000000000)) (hi := (4014531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2032375496417 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2032375496417 / 2000000000000) = 1/(250000000000 / 2032375496417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2095499663 / 1000000000) (2095499667 / 1000000000) (Real.log (2032375496417 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2032375496417 / 250000000000) = -Real.log (250000000000 / 2032375496417) := by
    rw [show ((2032375496417 / 250000000000) : ℝ) = ((250000000000 / 2032375496417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0219

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0220Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0220
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

theorem reflection_log_1_neg : (524173641 / 1000000000) ≤ -Real.log (640 / 1081) ∧
    -Real.log (640 / 1081) ≤ (262086821 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1721)) (n := 12)
    (lo := (524173641 / 1000000000)) (hi := (262086821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081 / 640) = 1/(640 / 1081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (524173641 / 1000000000) (262086821 / 500000000) (Real.log (1081 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1081 / 640) = -Real.log (640 / 1081) := by
    rw [show ((1081 / 640) : ℝ) = ((640 / 1081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1168163351 / 1000000000) ≤ -Real.log (199 / 640) ∧
    -Real.log (199 / 640) ≤ (1168163353 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 199) = 1/(199 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1168163353 / 1000000000) (-1168163351 / 1000000000) (Real.log (199 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65081523 / 125000000) ≤ -Real.log (1600 / 2693) ∧
    -Real.log (1600 / 2693) ≤ (104130437 / 200000000) := by
  have h := checkLog_sound (w := (1093 / 4293)) (n := 12)
    (lo := (65081523 / 125000000)) (hi := (104130437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2693 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2693 / 1600) = 1/(1600 / 2693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65081523 / 125000000) (104130437 / 200000000) (Real.log (2693 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2693 / 1600) = -Real.log (1600 / 2693) := by
    rw [show ((2693 / 1600) : ℝ) = ((1600 / 2693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (35913997 / 31250000) ≤ -Real.log (507 / 1600) ∧
    -Real.log (507 / 1600) ≤ (574623953 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 507) = 1/(507 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-574623953 / 500000000) (-35913997 / 31250000) (Real.log (507 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (487609 / 1562500) ≤ -Real.log (800 / 1093) ∧
    -Real.log (800 / 1093) ≤ (312069761 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1893)) (n := 12)
    (lo := (487609 / 1562500)) (hi := (312069761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093 / 800) = 1/(800 / 1093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (487609 / 1562500) (312069761 / 1000000000) (Real.log (1093 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1093 / 800) = -Real.log (800 / 1093) := by
    rw [show ((1093 / 800) : ℝ) = ((800 / 1093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114025181 / 250000000) ≤ -Real.log (507 / 800) ∧
    -Real.log (507 / 800) ≤ (18244029 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 507) = 1/(507 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-18244029 / 40000000) (-114025181 / 250000000) (Real.log (507 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (594162959 / 1000000000) ≤ -Real.log (500000 / 905757) ∧
    -Real.log (500000 / 905757) ≤ (7427037 / 12500000) := by
  have h := checkLog_sound (w := (405757 / 1405757)) (n := 12)
    (lo := (594162959 / 1000000000)) (hi := (7427037 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((905757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(905757 / 500000) = 1/(500000 / 905757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (594162959 / 1000000000) (7427037 / 12500000) (Real.log (905757 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (905757 / 500000) = -Real.log (500000 / 905757) := by
    rw [show ((905757 / 500000) : ℝ) = ((500000 / 905757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (208591443 / 125000000) ≤ -Real.log (94243 / 500000) ∧
    -Real.log (94243 / 500000) ≤ (1668731547 / 1000000000) := by
  have h := checkLog_sound (w := (30757 / 219243)) (n := 12)
    (lo := (4413081 / 15625000)) (hi := (56487437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94243) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 94243) = 1/(94243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1668731547 / 1000000000) (-208591443 / 125000000) (Real.log (94243 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119058463 / 200000000) ≤ -Real.log (1000000 / 1813561) ∧
    -Real.log (1000000 / 1813561) ≤ (148823079 / 250000000) := by
  have h := checkLog_sound (w := (813561 / 2813561)) (n := 12)
    (lo := (119058463 / 200000000)) (hi := (148823079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813561 / 1000000) = 1/(1000000 / 1813561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119058463 / 200000000) (148823079 / 250000000) (Real.log (1813561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1813561 / 1000000) = -Real.log (1000000 / 1813561) := by
    rw [show ((1813561 / 1000000) : ℝ) = ((1000000 / 1813561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (167965117 / 100000000) ≤ -Real.log (186439 / 1000000) ∧
    -Real.log (186439 / 1000000) ≤ (1679651173 / 1000000000) := by
  have h := checkLog_sound (w := (63561 / 436439)) (n := 12)
    (lo := (29335681 / 100000000)) (hi := (293356811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186439) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 186439) = 1/(186439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1679651173 / 1000000000) (-167965117 / 100000000) (Real.log (186439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (572841653 / 1000000000) ≤ -Real.log (1000000 / 1773299) ∧
    -Real.log (1000000 / 1773299) ≤ (286420827 / 500000000) := by
  have h := checkLog_sound (w := (773299 / 2773299)) (n := 12)
    (lo := (572841653 / 1000000000)) (hi := (286420827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773299 / 1000000) = 1/(1000000 / 1773299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (572841653 / 1000000000) (286420827 / 500000000) (Real.log (1773299 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1773299 / 1000000) = -Real.log (1000000 / 1773299) := by
    rw [show ((1773299 / 1000000) : ℝ) = ((1000000 / 1773299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1484123309 / 1000000000) ≤ -Real.log (226701 / 1000000) ∧
    -Real.log (226701 / 1000000) ≤ (92757707 / 62500000) := by
  have h := checkLog_sound (w := (23299 / 476701)) (n := 12)
    (lo := (97828949 / 1000000000)) (hi := (1956579 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226701) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 226701) = 1/(226701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-92757707 / 62500000) (-1484123309 / 1000000000) (Real.log (226701 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (574988449 / 1000000000) ≤ -Real.log (100000 / 177711) ∧
    -Real.log (100000 / 177711) ≤ (11499769 / 20000000) := by
  have h := checkLog_sound (w := (77711 / 277711)) (n := 12)
    (lo := (574988449 / 1000000000)) (hi := (11499769 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177711 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177711 / 100000) = 1/(100000 / 177711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (574988449 / 1000000000) (11499769 / 20000000) (Real.log (177711 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (177711 / 100000) = -Real.log (100000 / 177711) := by
    rw [show ((177711 / 100000) : ℝ) = ((100000 / 177711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1501076901 / 1000000000) ≤ -Real.log (22289 / 100000) ∧
    -Real.log (22289 / 100000) ≤ (187634613 / 125000000) := by
  have h := checkLog_sound (w := (2711 / 47289)) (n := 12)
    (lo := (114782541 / 1000000000)) (hi := (57391271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22289) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 22289) = 1/(22289 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-187634613 / 125000000) (-1501076901 / 1000000000) (Real.log (22289 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2262894503 / 1000000000) ≤ -Real.log (500000000000 / 4805433825323) ∧
    -Real.log (500000000000 / 4805433825323) ≤ (2262894507 / 1000000000) := by
  have h := checkLog_sound (w := (805433825323 / 8805433825323)) (n := 12)
    (lo := (183452963 / 1000000000)) (hi := (45863241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4805433825323 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4805433825323 / 4000000000000) = 1/(500000000000 / 4805433825323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2262894503 / 1000000000) (2262894507 / 1000000000) (Real.log (4805433825323 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4805433825323 / 500000000000) = -Real.log (500000000000 / 4805433825323) := by
    rw [show ((4805433825323 / 500000000000) : ℝ) = ((500000000000 / 4805433825323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (454988697 / 200000000) ≤ -Real.log (500000000000 / 4863684636799) ∧
    -Real.log (500000000000 / 4863684636799) ≤ (2274943489 / 1000000000) := by
  have h := checkLog_sound (w := (863684636799 / 8863684636799)) (n := 12)
    (lo := (39100389 / 200000000)) (hi := (97750973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4863684636799 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4863684636799 / 4000000000000) = 1/(500000000000 / 4863684636799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (454988697 / 200000000) (2274943489 / 1000000000) (Real.log (4863684636799 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4863684636799 / 500000000000) = -Real.log (500000000000 / 4863684636799) := by
    rw [show ((4863684636799 / 500000000000) : ℝ) = ((500000000000 / 4863684636799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1028482481 / 500000000) ≤ -Real.log (125000000000 / 977774138623) ∧
    -Real.log (125000000000 / 977774138623) ≤ (411392993 / 200000000) := by
  have h := checkLog_sound (w := (477774138623 / 1477774138623)) (n := 12)
    (lo := (335335301 / 500000000)) (hi := (670670603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977774138623 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(977774138623 / 500000000000) = 1/(125000000000 / 977774138623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1028482481 / 500000000) (411392993 / 200000000) (Real.log (977774138623 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (977774138623 / 125000000000) = -Real.log (125000000000 / 977774138623) := by
    rw [show ((977774138623 / 125000000000) : ℝ) = ((125000000000 / 977774138623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (41521307 / 20000000) ≤ -Real.log (50000000000 / 398651801337) ∧
    -Real.log (50000000000 / 398651801337) ≤ (2076065353 / 1000000000) := by
  have h := checkLog_sound (w := (198651801337 / 598651801337)) (n := 12)
    (lo := (68977099 / 100000000)) (hi := (689770991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398651801337 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(398651801337 / 200000000000) = 1/(50000000000 / 398651801337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (41521307 / 20000000) (2076065353 / 1000000000) (Real.log (398651801337 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (398651801337 / 50000000000) = -Real.log (50000000000 / 398651801337) := by
    rw [show ((398651801337 / 50000000000) : ℝ) = ((50000000000 / 398651801337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0220

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0221Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0221
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

theorem reflection_log_1_neg : (65081523 / 125000000) ≤ -Real.log (1600 / 2693) ∧
    -Real.log (1600 / 2693) ≤ (104130437 / 200000000) := by
  have h := checkLog_sound (w := (1093 / 4293)) (n := 12)
    (lo := (65081523 / 125000000)) (hi := (104130437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2693 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2693 / 1600) = 1/(1600 / 2693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65081523 / 125000000) (104130437 / 200000000) (Real.log (2693 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2693 / 1600) = -Real.log (1600 / 2693) := by
    rw [show ((2693 / 1600) : ℝ) = ((1600 / 2693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (35913997 / 31250000) ≤ -Real.log (507 / 1600) ∧
    -Real.log (507 / 1600) ≤ (574623953 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 507) = 1/(507 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-574623953 / 500000000) (-35913997 / 31250000) (Real.log (507 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (513571849 / 1000000000) ≤ -Real.log (800 / 1337) ∧
    -Real.log (800 / 1337) ≤ (10271437 / 20000000) := by
  have h := checkLog_sound (w := (537 / 2137)) (n := 12)
    (lo := (513571849 / 1000000000)) (hi := (10271437 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 800) = 1/(800 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (513571849 / 1000000000) (10271437 / 20000000) (Real.log (1337 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1337 / 800) = -Real.log (800 / 1337) := by
    rw [show ((1337 / 800) : ℝ) = ((800 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (556228847 / 500000000) ≤ -Real.log (263 / 800) ∧
    -Real.log (263 / 800) ≤ (34764303 / 31250000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 263) = 1/(263 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-34764303 / 31250000) (-556228847 / 500000000) (Real.log (263 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (487609 / 1562500) ≤ -Real.log (800 / 1093) ∧
    -Real.log (800 / 1093) ≤ (312069761 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1893)) (n := 12)
    (lo := (487609 / 1562500)) (hi := (312069761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093 / 800) = 1/(800 / 1093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (487609 / 1562500) (312069761 / 1000000000) (Real.log (1093 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1093 / 800) = -Real.log (800 / 1093) := by
    rw [show ((1093 / 800) : ℝ) = ((800 / 1093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114025181 / 250000000) ≤ -Real.log (507 / 800) ∧
    -Real.log (507 / 800) ≤ (18244029 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 507) = 1/(507 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-18244029 / 40000000) (-114025181 / 250000000) (Real.log (507 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (294533547 / 1000000000) ≤ -Real.log (400 / 537) ∧
    -Real.log (400 / 537) ≤ (73633387 / 250000000) := by
  have h := checkLog_sound (w := (137 / 937)) (n := 12)
    (lo := (294533547 / 1000000000)) (hi := (73633387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537 / 400) = 1/(400 / 537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (294533547 / 1000000000) (73633387 / 250000000) (Real.log (537 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (537 / 400) = -Real.log (400 / 537) := by
    rw [show ((537 / 400) : ℝ) = ((400 / 537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (209655257 / 500000000) ≤ -Real.log (263 / 400) ∧
    -Real.log (263 / 400) ≤ (83862103 / 200000000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 263) = 1/(263 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-83862103 / 200000000) (-209655257 / 500000000) (Real.log (263 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (592003317 / 1000000000) ≤ -Real.log (500000 / 903803) ∧
    -Real.log (500000 / 903803) ≤ (296001659 / 500000000) := by
  have h := checkLog_sound (w := (403803 / 1403803)) (n := 12)
    (lo := (592003317 / 1000000000)) (hi := (296001659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903803 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903803 / 500000) = 1/(500000 / 903803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (592003317 / 1000000000) (296001659 / 500000000) (Real.log (903803 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (903803 / 500000) = -Real.log (500000 / 903803) := by
    rw [show ((903803 / 500000) : ℝ) = ((500000 / 903803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (65928397 / 40000000) ≤ -Real.log (96197 / 500000) ∧
    -Real.log (96197 / 500000) ≤ (206026241 / 125000000) := by
  have h := checkLog_sound (w := (28803 / 221197)) (n := 12)
    (lo := (52383113 / 200000000)) (hi := (130957783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96197) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 96197) = 1/(96197 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-206026241 / 125000000) (-65928397 / 40000000) (Real.log (96197 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (594163511 / 1000000000) ≤ -Real.log (200000 / 362303) ∧
    -Real.log (200000 / 362303) ≤ (74270439 / 125000000) := by
  have h := checkLog_sound (w := (162303 / 562303)) (n := 12)
    (lo := (594163511 / 1000000000)) (hi := (74270439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362303 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362303 / 200000) = 1/(200000 / 362303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (594163511 / 1000000000) (74270439 / 125000000) (Real.log (362303 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (362303 / 200000) = -Real.log (200000 / 362303) := by
    rw [show ((362303 / 200000) : ℝ) = ((200000 / 362303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1668736849 / 1000000000) ≤ -Real.log (37697 / 200000) ∧
    -Real.log (37697 / 200000) ≤ (417184213 / 250000000) := by
  have h := checkLog_sound (w := (12303 / 87697)) (n := 12)
    (lo := (282442489 / 1000000000)) (hi := (28244249 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37697) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 37697) = 1/(37697 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-417184213 / 250000000) (-1668736849 / 1000000000) (Real.log (37697 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (142137511 / 250000000) ≤ -Real.log (200000 / 353141) ∧
    -Real.log (200000 / 353141) ≤ (113710009 / 200000000) := by
  have h := checkLog_sound (w := (153141 / 553141)) (n := 12)
    (lo := (142137511 / 250000000)) (hi := (113710009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353141 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353141 / 200000) = 1/(200000 / 353141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (142137511 / 250000000) (113710009 / 200000000) (Real.log (353141 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (353141 / 200000) = -Real.log (200000 / 353141) := by
    rw [show ((353141 / 200000) : ℝ) = ((200000 / 353141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (11337299 / 7812500) ≤ -Real.log (46859 / 200000) ∧
    -Real.log (46859 / 200000) ≤ (58046971 / 40000000) := by
  have h := checkLog_sound (w := (3141 / 96859)) (n := 12)
    (lo := (8109989 / 125000000)) (hi := (64879913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46859) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 46859) = 1/(46859 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-58046971 / 40000000) (-11337299 / 7812500) (Real.log (46859 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (572842217 / 1000000000) ≤ -Real.log (10000 / 17733) ∧
    -Real.log (10000 / 17733) ≤ (286421109 / 500000000) := by
  have h := checkLog_sound (w := (7733 / 27733)) (n := 12)
    (lo := (572842217 / 1000000000)) (hi := (286421109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17733 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17733 / 10000) = 1/(10000 / 17733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (572842217 / 1000000000) (286421109 / 500000000) (Real.log (17733 / 10000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (17733 / 10000) = -Real.log (10000 / 17733) := by
    rw [show ((17733 / 10000) : ℝ) = ((10000 / 17733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37103193 / 25000000) ≤ -Real.log (2267 / 10000) ∧
    -Real.log (2267 / 10000) ≤ (1484127723 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 4767)) (n := 12)
    (lo := (1222917 / 12500000)) (hi := (97833361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2267) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2500 / 2267) = 1/(2267 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1484127723 / 1000000000) (-37103193 / 25000000) (Real.log (2267 / 10000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1120106621 / 500000000) ≤ -Real.log (500000000000 / 4697667286921) ∧
    -Real.log (500000000000 / 4697667286921) ≤ (1120106623 / 500000000) := by
  have h := checkLog_sound (w := (697667286921 / 8697667286921)) (n := 12)
    (lo := (80385851 / 500000000)) (hi := (160771703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4697667286921 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4697667286921 / 4000000000000) = 1/(500000000000 / 4697667286921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1120106621 / 500000000) (1120106623 / 500000000) (Real.log (4697667286921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4697667286921 / 500000000000) = -Real.log (500000000000 / 4697667286921) := by
    rw [show ((4697667286921 / 500000000000) : ℝ) = ((500000000000 / 4697667286921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (56572509 / 25000000) ≤ -Real.log (250000000000 / 2402730986551) ∧
    -Real.log (250000000000 / 2402730986551) ≤ (565725091 / 250000000) := by
  have h := checkLog_sound (w := (402730986551 / 4402730986551)) (n := 12)
    (lo := (9172941 / 50000000)) (hi := (183458821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2402730986551 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2402730986551 / 2000000000000) = 1/(250000000000 / 2402730986551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (56572509 / 25000000) (565725091 / 250000000) (Real.log (2402730986551 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2402730986551 / 250000000000) = -Real.log (250000000000 / 2402730986551) := by
    rw [show ((2402730986551 / 250000000000) : ℝ) = ((250000000000 / 2402730986551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (504931079 / 250000000) ≤ -Real.log (250000000000 / 1884061759747) ∧
    -Real.log (250000000000 / 1884061759747) ≤ (2019724319 / 1000000000) := by
  have h := checkLog_sound (w := (884061759747 / 2884061759747)) (n := 12)
    (lo := (158357489 / 250000000)) (hi := (633429957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1884061759747 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1884061759747 / 1000000000000) = 1/(250000000000 / 1884061759747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (504931079 / 250000000) (2019724319 / 1000000000) (Real.log (1884061759747 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1884061759747 / 250000000000) = -Real.log (250000000000 / 1884061759747) := by
    rw [show ((1884061759747 / 250000000000) : ℝ) = ((250000000000 / 1884061759747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2056969937 / 1000000000) ≤ -Real.log (7812500000 / 61111187693) ∧
    -Real.log (7812500000 / 61111187693) ≤ (102848497 / 50000000) := by
  have h := checkLog_sound (w := (29861187693 / 92361187693)) (n := 12)
    (lo := (670675577 / 1000000000)) (hi := (335337789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61111187693 / 31250000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(61111187693 / 31250000000) = 1/(7812500000 / 61111187693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2056969937 / 1000000000) (102848497 / 50000000) (Real.log (61111187693 / 7812500000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (61111187693 / 7812500000) = -Real.log (7812500000 / 61111187693) := by
    rw [show ((61111187693 / 7812500000) : ℝ) = ((7812500000 / 61111187693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0221

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0222Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0222
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

theorem reflection_log_1_neg : (513571849 / 1000000000) ≤ -Real.log (800 / 1337) ∧
    -Real.log (800 / 1337) ≤ (10271437 / 20000000) := by
  have h := checkLog_sound (w := (537 / 2137)) (n := 12)
    (lo := (513571849 / 1000000000)) (hi := (10271437 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 800) = 1/(800 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (513571849 / 1000000000) (10271437 / 20000000) (Real.log (1337 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1337 / 800) = -Real.log (800 / 1337) := by
    rw [show ((1337 / 800) : ℝ) = ((800 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (556228847 / 500000000) ≤ -Real.log (263 / 800) ∧
    -Real.log (263 / 800) ≤ (34764303 / 31250000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 263) = 1/(263 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-34764303 / 31250000) (-556228847 / 500000000) (Real.log (263 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20257641 / 40000000) ≤ -Real.log (320 / 531) ∧
    -Real.log (320 / 531) ≤ (253220513 / 500000000) := by
  have h := checkLog_sound (w := (211 / 851)) (n := 12)
    (lo := (20257641 / 40000000)) (hi := (253220513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(531 / 320) = 1/(320 / 531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20257641 / 40000000) (253220513 / 500000000) (Real.log (531 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (531 / 320) = -Real.log (320 / 531) := by
    rw [show ((531 / 320) : ℝ) = ((320 / 531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1076973113 / 1000000000) ≤ -Real.log (109 / 320) ∧
    -Real.log (109 / 320) ≤ (215394623 / 200000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 109) = 1/(109 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-215394623 / 200000000) (-1076973113 / 1000000000) (Real.log (109 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (294533547 / 1000000000) ≤ -Real.log (400 / 537) ∧
    -Real.log (400 / 537) ≤ (73633387 / 250000000) := by
  have h := checkLog_sound (w := (137 / 937)) (n := 12)
    (lo := (294533547 / 1000000000)) (hi := (73633387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537 / 400) = 1/(400 / 537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (294533547 / 1000000000) (73633387 / 250000000) (Real.log (537 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (537 / 400) = -Real.log (400 / 537) := by
    rw [show ((537 / 400) : ℝ) = ((400 / 537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (209655257 / 500000000) ≤ -Real.log (263 / 400) ∧
    -Real.log (263 / 400) ≤ (83862103 / 200000000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 263) = 1/(263 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-83862103 / 200000000) (-209655257 / 500000000) (Real.log (263 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (138342159 / 500000000) ≤ -Real.log (160 / 211) ∧
    -Real.log (160 / 211) ≤ (276684319 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 371)) (n := 12)
    (lo := (138342159 / 500000000)) (hi := (276684319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 160) = 1/(160 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (138342159 / 500000000) (276684319 / 1000000000) (Real.log (211 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (211 / 160) = -Real.log (160 / 211) := by
    rw [show ((211 / 160) : ℝ) = ((160 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (383825933 / 1000000000) ≤ -Real.log (109 / 160) ∧
    -Real.log (109 / 160) ≤ (191912967 / 500000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 109) = 1/(109 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-191912967 / 500000000) (-383825933 / 1000000000) (Real.log (109 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (294988521 / 500000000) ≤ -Real.log (1000000 / 1803947) ∧
    -Real.log (1000000 / 1803947) ≤ (589977043 / 1000000000) := by
  have h := checkLog_sound (w := (803947 / 2803947)) (n := 12)
    (lo := (294988521 / 500000000)) (hi := (589977043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1803947 / 1000000) = 1/(1000000 / 1803947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (294988521 / 500000000) (589977043 / 1000000000) (Real.log (1803947 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1803947 / 1000000) = -Real.log (1000000 / 1803947) := by
    rw [show ((1803947 / 1000000) : ℝ) = ((1000000 / 1803947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1629370247 / 1000000000) ≤ -Real.log (196053 / 1000000) ∧
    -Real.log (196053 / 1000000) ≤ (6517481 / 4000000) := by
  have h := checkLog_sound (w := (53947 / 446053)) (n := 12)
    (lo := (243075887 / 1000000000)) (hi := (15192243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196053) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 196053) = 1/(196053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6517481 / 4000000) (-1629370247 / 1000000000) (Real.log (196053 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (592003871 / 1000000000) ≤ -Real.log (1000000 / 1807607) ∧
    -Real.log (1000000 / 1807607) ≤ (18500121 / 31250000) := by
  have h := checkLog_sound (w := (807607 / 2807607)) (n := 12)
    (lo := (592003871 / 1000000000)) (hi := (18500121 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1807607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1807607 / 1000000) = 1/(1000000 / 1807607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (592003871 / 1000000000) (18500121 / 31250000) (Real.log (1807607 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1807607 / 1000000) = -Real.log (1000000 / 1807607) := by
    rw [show ((1807607 / 1000000) : ℝ) = ((1000000 / 1807607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (824107561 / 500000000) ≤ -Real.log (192393 / 1000000) ∧
    -Real.log (192393 / 1000000) ≤ (13185721 / 8000000) := by
  have h := checkLog_sound (w := (57607 / 442393)) (n := 12)
    (lo := (130960381 / 500000000)) (hi := (261920763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192393) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 192393) = 1/(192393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-13185721 / 8000000) (-824107561 / 500000000) (Real.log (192393 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (141064961 / 250000000) ≤ -Real.log (500000 / 879073) ∧
    -Real.log (500000 / 879073) ≤ (112851969 / 200000000) := by
  have h := checkLog_sound (w := (379073 / 1379073)) (n := 12)
    (lo := (141064961 / 250000000)) (hi := (112851969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879073 / 500000) = 1/(500000 / 879073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (141064961 / 250000000) (112851969 / 200000000) (Real.log (879073 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (879073 / 500000) = -Real.log (500000 / 879073) := by
    rw [show ((879073 / 500000) : ℝ) = ((500000 / 879073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1419421039 / 1000000000) ≤ -Real.log (120927 / 500000) ∧
    -Real.log (120927 / 500000) ≤ (709710521 / 500000000) := by
  have h := checkLog_sound (w := (4073 / 245927)) (n := 12)
    (lo := (33126679 / 1000000000)) (hi := (828167 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 120927) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 120927) = 1/(120927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-709710521 / 500000000) (-1419421039 / 1000000000) (Real.log (120927 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (56855061 / 100000000) ≤ -Real.log (500000 / 882853) ∧
    -Real.log (500000 / 882853) ≤ (568550611 / 1000000000) := by
  have h := checkLog_sound (w := (382853 / 1382853)) (n := 12)
    (lo := (56855061 / 100000000)) (hi := (568550611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((882853 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(882853 / 500000) = 1/(500000 / 882853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56855061 / 100000000) (568550611 / 1000000000) (Real.log (882853 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (882853 / 500000) = -Real.log (500000 / 882853) := by
    rw [show ((882853 / 500000) : ℝ) = ((500000 / 882853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (72558927 / 50000000) ≤ -Real.log (117147 / 500000) ∧
    -Real.log (117147 / 500000) ≤ (1451178543 / 1000000000) := by
  have h := checkLog_sound (w := (7853 / 242147)) (n := 12)
    (lo := (3244209 / 50000000)) (hi := (64884181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 117147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 117147) = 1/(117147 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1451178543 / 1000000000) (-72558927 / 50000000) (Real.log (117147 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (277418411 / 125000000) ≤ -Real.log (500000000000 / 4600661555803) ∧
    -Real.log (500000000000 / 4600661555803) ≤ (554836823 / 250000000) := by
  have h := checkLog_sound (w := (600661555803 / 8600661555803)) (n := 12)
    (lo := (34976437 / 250000000)) (hi := (139905749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4600661555803 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4600661555803 / 4000000000000) = 1/(500000000000 / 4600661555803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (277418411 / 125000000) (554836823 / 250000000) (Real.log (4600661555803 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4600661555803 / 500000000000) = -Real.log (500000000000 / 4600661555803) := by
    rw [show ((4600661555803 / 500000000000) : ℝ) = ((500000000000 / 4600661555803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2240218993 / 1000000000) ≤ -Real.log (62500000000 / 587211787851) ∧
    -Real.log (62500000000 / 587211787851) ≤ (2240218997 / 1000000000) := by
  have h := checkLog_sound (w := (87211787851 / 1087211787851)) (n := 12)
    (lo := (160777453 / 1000000000)) (hi := (80388727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587211787851 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(587211787851 / 500000000000) = 1/(62500000000 / 587211787851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2240218993 / 1000000000) (2240218997 / 1000000000) (Real.log (587211787851 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (587211787851 / 62500000000) = -Real.log (62500000000 / 587211787851) := by
    rw [show ((587211787851 / 62500000000) : ℝ) = ((62500000000 / 587211787851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (495920221 / 250000000) ≤ -Real.log (500000000000 / 3634725909019) ∧
    -Real.log (500000000000 / 3634725909019) ≤ (1983680887 / 1000000000) := by
  have h := checkLog_sound (w := (1634725909019 / 5634725909019)) (n := 12)
    (lo := (149346631 / 250000000)) (hi := (23895461 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3634725909019 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3634725909019 / 2000000000000) = 1/(500000000000 / 3634725909019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (495920221 / 250000000) (1983680887 / 1000000000) (Real.log (3634725909019 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3634725909019 / 500000000000) = -Real.log (500000000000 / 3634725909019) := by
    rw [show ((3634725909019 / 500000000000) : ℝ) = ((500000000000 / 3634725909019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2019729151 / 1000000000) ≤ -Real.log (500000000000 / 3768141736451) ∧
    -Real.log (500000000000 / 3768141736451) ≤ (1009864577 / 500000000) := by
  have h := checkLog_sound (w := (1768141736451 / 5768141736451)) (n := 12)
    (lo := (633434791 / 1000000000)) (hi := (79179349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3768141736451 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3768141736451 / 2000000000000) = 1/(500000000000 / 3768141736451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2019729151 / 1000000000) (1009864577 / 500000000) (Real.log (3768141736451 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3768141736451 / 500000000000) = -Real.log (500000000000 / 3768141736451) := by
    rw [show ((3768141736451 / 500000000000) : ℝ) = ((500000000000 / 3768141736451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0222

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0223Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0223
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

theorem reflection_log_1_neg : (20257641 / 40000000) ≤ -Real.log (320 / 531) ∧
    -Real.log (320 / 531) ≤ (253220513 / 500000000) := by
  have h := checkLog_sound (w := (211 / 851)) (n := 12)
    (lo := (20257641 / 40000000)) (hi := (253220513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(531 / 320) = 1/(320 / 531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20257641 / 40000000) (253220513 / 500000000) (Real.log (531 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (531 / 320) = -Real.log (320 / 531) := by
    rw [show ((531 / 320) : ℝ) = ((320 / 531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1076973113 / 1000000000) ≤ -Real.log (109 / 320) ∧
    -Real.log (109 / 320) ≤ (215394623 / 200000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 109) = 1/(109 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-215394623 / 200000000) (-1076973113 / 1000000000) (Real.log (109 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (499258987 / 1000000000) ≤ -Real.log (400 / 659) ∧
    -Real.log (400 / 659) ≤ (124814747 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1059)) (n := 12)
    (lo := (499258987 / 1000000000)) (hi := (124814747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659 / 400) = 1/(400 / 659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (499258987 / 1000000000) (124814747 / 250000000) (Real.log (659 / 400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (659 / 400) = -Real.log (400 / 659) := by
    rw [show ((659 / 400) : ℝ) = ((400 / 659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65169041 / 62500000) ≤ -Real.log (141 / 400) ∧
    -Real.log (141 / 400) ≤ (521352329 / 500000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 141) = 1/(141 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-521352329 / 500000000) (-65169041 / 62500000) (Real.log (141 / 400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (138342159 / 500000000) ≤ -Real.log (160 / 211) ∧
    -Real.log (160 / 211) ≤ (276684319 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 371)) (n := 12)
    (lo := (138342159 / 500000000)) (hi := (276684319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 160) = 1/(160 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (138342159 / 500000000) (276684319 / 1000000000) (Real.log (211 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (211 / 160) = -Real.log (160 / 211) := by
    rw [show ((211 / 160) : ℝ) = ((160 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (383825933 / 1000000000) ≤ -Real.log (109 / 160) ∧
    -Real.log (109 / 160) ≤ (191912967 / 500000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 109) = 1/(109 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-191912967 / 500000000) (-383825933 / 1000000000) (Real.log (109 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (51702139 / 200000000) ≤ -Real.log (200 / 259) ∧
    -Real.log (200 / 259) ≤ (32313837 / 125000000) := by
  have h := checkLog_sound (w := (59 / 459)) (n := 12)
    (lo := (51702139 / 200000000)) (hi := (32313837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259 / 200) = 1/(200 / 259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (51702139 / 200000000) (32313837 / 125000000) (Real.log (259 / 200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (259 / 200) = -Real.log (200 / 259) := by
    rw [show ((259 / 200) : ℝ) = ((200 / 259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (87389369 / 250000000) ≤ -Real.log (141 / 200) ∧
    -Real.log (141 / 200) ≤ (349557477 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 141) = 1/(141 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-349557477 / 1000000000) (-87389369 / 250000000) (Real.log (141 / 200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36755379 / 62500000) ≤ -Real.log (1000000 / 1800539) ∧
    -Real.log (1000000 / 1800539) ≤ (117617213 / 200000000) := by
  have h := checkLog_sound (w := (800539 / 2800539)) (n := 12)
    (lo := (36755379 / 62500000)) (hi := (117617213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1800539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1800539 / 1000000) = 1/(1000000 / 1800539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36755379 / 62500000) (117617213 / 200000000) (Real.log (1800539 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1800539 / 1000000) = -Real.log (1000000 / 1800539) := by
    rw [show ((1800539 / 1000000) : ℝ) = ((1000000 / 1800539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1612136549 / 1000000000) ≤ -Real.log (199461 / 1000000) ∧
    -Real.log (199461 / 1000000) ≤ (201517069 / 125000000) := by
  have h := checkLog_sound (w := (50539 / 449461)) (n := 12)
    (lo := (225842189 / 1000000000)) (hi := (22584219 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199461) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 199461) = 1/(199461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-201517069 / 125000000) (-1612136549 / 1000000000) (Real.log (199461 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (147494399 / 250000000) ≤ -Real.log (250000 / 450987) ∧
    -Real.log (250000 / 450987) ≤ (589977597 / 1000000000) := by
  have h := checkLog_sound (w := (200987 / 700987)) (n := 12)
    (lo := (147494399 / 250000000)) (hi := (589977597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450987 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450987 / 250000) = 1/(250000 / 450987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (147494399 / 250000000) (589977597 / 1000000000) (Real.log (450987 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (450987 / 250000) = -Real.log (250000 / 450987) := by
    rw [show ((450987 / 250000) : ℝ) = ((250000 / 450987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1629375347 / 1000000000) ≤ -Real.log (49013 / 250000) ∧
    -Real.log (49013 / 250000) ≤ (32587507 / 20000000) := by
  have h := checkLog_sound (w := (13487 / 111513)) (n := 12)
    (lo := (243080987 / 1000000000)) (hi := (60770247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49013) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 49013) = 1/(49013 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-32587507 / 20000000) (-1629375347 / 1000000000) (Real.log (49013 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (139992217 / 250000000) ≤ -Real.log (500000 / 875309) ∧
    -Real.log (500000 / 875309) ≤ (559968869 / 1000000000) := by
  have h := checkLog_sound (w := (375309 / 1375309)) (n := 12)
    (lo := (139992217 / 250000000)) (hi := (559968869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875309 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875309 / 500000) = 1/(500000 / 875309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (139992217 / 250000000) (559968869 / 1000000000) (Real.log (875309 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (875309 / 500000) = -Real.log (500000 / 875309) := by
    rw [show ((875309 / 500000) : ℝ) = ((500000 / 875309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69438471 / 50000000) ≤ -Real.log (124691 / 500000) ∧
    -Real.log (124691 / 500000) ≤ (1388769423 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 249691)) (n := 12)
    (lo := (123753 / 50000000)) (hi := (2475061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124691) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 124691) = 1/(124691 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1388769423 / 1000000000) (-69438471 / 50000000) (Real.log (124691 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (564260413 / 1000000000) ≤ -Real.log (1000000 / 1758147) ∧
    -Real.log (1000000 / 1758147) ≤ (282130207 / 500000000) := by
  have h := checkLog_sound (w := (758147 / 2758147)) (n := 12)
    (lo := (564260413 / 1000000000)) (hi := (282130207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1758147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1758147 / 1000000) = 1/(1000000 / 1758147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (564260413 / 1000000000) (282130207 / 500000000) (Real.log (1758147 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1758147 / 1000000) = -Real.log (1000000 / 1758147) := by
    rw [show ((1758147 / 1000000) : ℝ) = ((1000000 / 1758147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (709712587 / 500000000) ≤ -Real.log (241853 / 1000000) ∧
    -Real.log (241853 / 1000000) ≤ (1419425177 / 1000000000) := by
  have h := checkLog_sound (w := (8147 / 491853)) (n := 12)
    (lo := (16565407 / 500000000)) (hi := (6626163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 241853) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 241853) = 1/(241853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1419425177 / 1000000000) (-709712587 / 500000000) (Real.log (241853 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2200222613 / 1000000000) ≤ -Real.log (250000000000 / 2256755706629) ∧
    -Real.log (250000000000 / 2256755706629) ≤ (2200222617 / 1000000000) := by
  have h := checkLog_sound (w := (256755706629 / 4256755706629)) (n := 12)
    (lo := (120781073 / 1000000000)) (hi := (60390537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2256755706629 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2256755706629 / 2000000000000) = 1/(250000000000 / 2256755706629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2200222613 / 1000000000) (2200222617 / 1000000000) (Real.log (2256755706629 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2256755706629 / 250000000000) = -Real.log (250000000000 / 2256755706629) := by
    rw [show ((2256755706629 / 250000000000) : ℝ) = ((250000000000 / 2256755706629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2219352943 / 1000000000) ≤ -Real.log (100000000000 / 920137514537) ∧
    -Real.log (100000000000 / 920137514537) ≤ (2219352947 / 1000000000) := by
  have h := checkLog_sound (w := (120137514537 / 1720137514537)) (n := 12)
    (lo := (139911403 / 1000000000)) (hi := (34977851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920137514537 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(920137514537 / 800000000000) = 1/(100000000000 / 920137514537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2219352943 / 1000000000) (2219352947 / 1000000000) (Real.log (920137514537 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (920137514537 / 100000000000) = -Real.log (100000000000 / 920137514537) := by
    rw [show ((920137514537 / 100000000000) : ℝ) = ((100000000000 / 920137514537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (121796143 / 62500000) ≤ -Real.log (500000000000 / 3509912503709) ∧
    -Real.log (500000000000 / 3509912503709) ≤ (1948738291 / 1000000000) := by
  have h := checkLog_sound (w := (1509912503709 / 5509912503709)) (n := 12)
    (lo := (70305491 / 125000000)) (hi := (562443929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3509912503709 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3509912503709 / 2000000000000) = 1/(500000000000 / 3509912503709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (121796143 / 62500000) (1948738291 / 1000000000) (Real.log (3509912503709 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3509912503709 / 500000000000) = -Real.log (500000000000 / 3509912503709) := by
    rw [show ((3509912503709 / 500000000000) : ℝ) = ((500000000000 / 3509912503709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1983685587 / 1000000000) ≤ -Real.log (500000000000 / 3634743005049) ∧
    -Real.log (500000000000 / 3634743005049) ≤ (198368559 / 100000000) := by
  have h := checkLog_sound (w := (1634743005049 / 5634743005049)) (n := 12)
    (lo := (597391227 / 1000000000)) (hi := (149347807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3634743005049 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3634743005049 / 2000000000000) = 1/(500000000000 / 3634743005049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1983685587 / 1000000000) (198368559 / 100000000) (Real.log (3634743005049 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3634743005049 / 500000000000) = -Real.log (500000000000 / 3634743005049) := by
    rw [show ((3634743005049 / 500000000000) : ℝ) = ((500000000000 / 3634743005049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0223

end


