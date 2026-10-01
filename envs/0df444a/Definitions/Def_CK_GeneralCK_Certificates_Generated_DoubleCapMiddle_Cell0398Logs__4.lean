-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0398Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0398Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:31:15.000446+00:00
-- url     : https://prove2.me/theorems/b3ff45a6-1e47-48c1-a88c-5c5515dfea0b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0400Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0401Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0400Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0401Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0400Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0401Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0398Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0399Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0400Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0401Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0398
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

theorem reflection_log_1_neg : (100353103 / 500000000) ≤ -Real.log (2560 / 3129) ∧
    -Real.log (2560 / 3129) ≤ (200706207 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 5689)) (n := 12)
    (lo := (100353103 / 500000000)) (hi := (200706207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3129 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3129 / 2560) = 1/(2560 / 3129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (100353103 / 500000000) (200706207 / 1000000000) (Real.log (3129 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3129 / 2560) = -Real.log (2560 / 3129) := by
    rw [show ((3129 / 2560) : ℝ) = ((2560 / 3129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (251370233 / 1000000000) ≤ -Real.log (1991 / 2560) ∧
    -Real.log (1991 / 2560) ≤ (125685117 / 500000000) := by
  have h := checkLog_sound (w := (569 / 4551)) (n := 12)
    (lo := (251370233 / 1000000000)) (hi := (125685117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1991) = 1/(1991 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-125685117 / 500000000) (-251370233 / 1000000000) (Real.log (1991 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50116621 / 250000000) ≤ -Real.log (10240 / 12513) ∧
    -Real.log (10240 / 12513) ≤ (40093297 / 200000000) := by
  have h := checkLog_sound (w := (2273 / 22753)) (n := 12)
    (lo := (50116621 / 250000000)) (hi := (40093297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12513 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12513 / 10240) = 1/(10240 / 12513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50116621 / 250000000) (40093297 / 200000000) (Real.log (12513 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12513 / 10240) = -Real.log (10240 / 12513) := by
    rw [show ((12513 / 10240) : ℝ) = ((10240 / 12513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (250993609 / 1000000000) ≤ -Real.log (7967 / 10240) ∧
    -Real.log (7967 / 10240) ≤ (25099361 / 100000000) := by
  have h := checkLog_sound (w := (2273 / 18207)) (n := 12)
    (lo := (250993609 / 1000000000)) (hi := (25099361 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7967) = 1/(7967 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-25099361 / 100000000) (-250993609 / 1000000000) (Real.log (7967 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183892437 / 500000000) ≤ -Real.log (1280 / 1849) ∧
    -Real.log (1280 / 1849) ≤ (2942279 / 8000000) := by
  have h := checkLog_sound (w := (569 / 3129)) (n := 12)
    (lo := (183892437 / 500000000)) (hi := (2942279 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1849 / 1280) = 1/(1280 / 1849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183892437 / 500000000) (2942279 / 8000000) (Real.log (1849 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1849 / 1280) = -Real.log (1280 / 1849) := by
    rw [show ((1849 / 1280) : ℝ) = ((1280 / 1849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (587942927 / 1000000000) ≤ -Real.log (711 / 1280) ∧
    -Real.log (711 / 1280) ≤ (36746433 / 62500000) := by
  have h := checkLog_sound (w := (569 / 1991)) (n := 12)
    (lo := (587942927 / 1000000000)) (hi := (36746433 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 711) = 1/(711 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-36746433 / 62500000) (-587942927 / 1000000000) (Real.log (711 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (367379167 / 1000000000) ≤ -Real.log (5120 / 7393) ∧
    -Real.log (5120 / 7393) ≤ (11480599 / 31250000) := by
  have h := checkLog_sound (w := (2273 / 12513)) (n := 12)
    (lo := (367379167 / 1000000000)) (hi := (11480599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7393 / 5120) = 1/(5120 / 7393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (367379167 / 1000000000) (11480599 / 31250000) (Real.log (7393 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7393 / 5120) = -Real.log (5120 / 7393) := by
    rw [show ((7393 / 5120) : ℝ) = ((5120 / 7393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58688863 / 100000000) ≤ -Real.log (2847 / 5120) ∧
    -Real.log (2847 / 5120) ≤ (586888631 / 1000000000) := by
  have h := checkLog_sound (w := (2273 / 7967)) (n := 12)
    (lo := (58688863 / 100000000)) (hi := (586888631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2847) = 1/(2847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-586888631 / 1000000000) (-58688863 / 100000000) (Real.log (2847 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27515139 / 100000000) ≤ -Real.log (100000 / 131673) ∧
    -Real.log (100000 / 131673) ≤ (275151391 / 1000000000) := by
  have h := checkLog_sound (w := (31673 / 231673)) (n := 12)
    (lo := (27515139 / 100000000)) (hi := (275151391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131673 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131673 / 100000) = 1/(100000 / 131673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27515139 / 100000000) (275151391 / 1000000000) (Real.log (131673 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (131673 / 100000) = -Real.log (100000 / 131673) := by
    rw [show ((131673 / 100000) : ℝ) = ((100000 / 131673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190432591 / 500000000) ≤ -Real.log (68327 / 100000) ∧
    -Real.log (68327 / 100000) ≤ (380865183 / 1000000000) := by
  have h := checkLog_sound (w := (31673 / 168327)) (n := 12)
    (lo := (190432591 / 500000000)) (hi := (380865183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68327) = 1/(68327 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-380865183 / 1000000000) (-190432591 / 500000000) (Real.log (68327 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (440761 / 1600000) ≤ -Real.log (1000000 / 1317157) ∧
    -Real.log (1000000 / 1317157) ≤ (137737813 / 500000000) := by
  have h := checkLog_sound (w := (317157 / 2317157)) (n := 12)
    (lo := (440761 / 1600000)) (hi := (137737813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317157 / 1000000) = 1/(1000000 / 1317157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (440761 / 1600000) (137737813 / 500000000) (Real.log (1317157 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1317157 / 1000000) = -Real.log (1000000 / 1317157) := by
    rw [show ((1317157 / 1000000) : ℝ) = ((1000000 / 1317157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (190745157 / 500000000) ≤ -Real.log (682843 / 1000000) ∧
    -Real.log (682843 / 1000000) ≤ (76298063 / 200000000) := by
  have h := checkLog_sound (w := (317157 / 1682843)) (n := 12)
    (lo := (190745157 / 500000000)) (hi := (76298063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682843) = 1/(682843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76298063 / 200000000) (-190745157 / 500000000) (Real.log (682843 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51826499 / 250000000) ≤ -Real.log (1000000 / 1230359) ∧
    -Real.log (1000000 / 1230359) ≤ (207305997 / 1000000000) := by
  have h := checkLog_sound (w := (230359 / 2230359)) (n := 12)
    (lo := (51826499 / 250000000)) (hi := (207305997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230359 / 1000000) = 1/(1000000 / 1230359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51826499 / 250000000) (207305997 / 1000000000) (Real.log (1230359 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1230359 / 1000000) = -Real.log (1000000 / 1230359) := by
    rw [show ((1230359 / 1000000) : ℝ) = ((1000000 / 1230359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (130915553 / 500000000) ≤ -Real.log (769641 / 1000000) ∧
    -Real.log (769641 / 1000000) ≤ (261831107 / 1000000000) := by
  have h := checkLog_sound (w := (230359 / 1769641)) (n := 12)
    (lo := (130915553 / 500000000)) (hi := (261831107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769641) = 1/(769641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-261831107 / 1000000000) (-130915553 / 500000000) (Real.log (769641 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (103786681 / 500000000) ≤ -Real.log (31250 / 38459) ∧
    -Real.log (31250 / 38459) ≤ (207573363 / 1000000000) := by
  have h := checkLog_sound (w := (7209 / 69709)) (n := 12)
    (lo := (103786681 / 500000000)) (hi := (207573363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38459 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38459 / 31250) = 1/(31250 / 38459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103786681 / 500000000) (207573363 / 1000000000) (Real.log (38459 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38459 / 31250) = -Real.log (31250 / 38459) := by
    rw [show ((38459 / 31250) : ℝ) = ((31250 / 38459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (26225867 / 100000000) ≤ -Real.log (24041 / 31250) ∧
    -Real.log (24041 / 31250) ≤ (262258671 / 1000000000) := by
  have h := checkLog_sound (w := (7209 / 55291)) (n := 12)
    (lo := (26225867 / 100000000)) (hi := (262258671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24041) = 1/(24041 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-262258671 / 1000000000) (-26225867 / 100000000) (Real.log (24041 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (656016573 / 1000000000) ≤ -Real.log (500000000000 / 963550280269) ∧
    -Real.log (500000000000 / 963550280269) ≤ (328008287 / 500000000) := by
  have h := checkLog_sound (w := (463550280269 / 1463550280269)) (n := 12)
    (lo := (656016573 / 1000000000)) (hi := (328008287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963550280269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963550280269 / 500000000000) = 1/(500000000000 / 963550280269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (656016573 / 1000000000) (328008287 / 500000000) (Real.log (963550280269 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (963550280269 / 500000000000) = -Real.log (500000000000 / 963550280269) := by
    rw [show ((963550280269 / 500000000000) : ℝ) = ((500000000000 / 963550280269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32848297 / 50000000) ≤ -Real.log (31250000000 / 60279092339) ∧
    -Real.log (31250000000 / 60279092339) ≤ (656965941 / 1000000000) := by
  have h := checkLog_sound (w := (29029092339 / 91529092339)) (n := 12)
    (lo := (32848297 / 50000000)) (hi := (656965941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60279092339 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60279092339 / 31250000000) = 1/(31250000000 / 60279092339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32848297 / 50000000) (656965941 / 1000000000) (Real.log (60279092339 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (60279092339 / 31250000000) = -Real.log (31250000000 / 60279092339) := by
    rw [show ((60279092339 / 31250000000) : ℝ) = ((31250000000 / 60279092339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (469137103 / 1000000000) ≤ -Real.log (250000000000 / 399653539767) ∧
    -Real.log (250000000000 / 399653539767) ≤ (29321069 / 62500000) := by
  have h := checkLog_sound (w := (149653539767 / 649653539767)) (n := 12)
    (lo := (469137103 / 1000000000)) (hi := (29321069 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399653539767 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399653539767 / 250000000000) = 1/(250000000000 / 399653539767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (469137103 / 1000000000) (29321069 / 62500000) (Real.log (399653539767 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (399653539767 / 250000000000) = -Real.log (250000000000 / 399653539767) := by
    rw [show ((399653539767 / 250000000000) : ℝ) = ((250000000000 / 399653539767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14682251 / 31250000) ≤ -Real.log (15625000000 / 24995710453) ∧
    -Real.log (15625000000 / 24995710453) ≤ (469832033 / 1000000000) := by
  have h := checkLog_sound (w := (9370710453 / 40620710453)) (n := 12)
    (lo := (14682251 / 31250000)) (hi := (469832033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24995710453 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24995710453 / 15625000000) = 1/(15625000000 / 24995710453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14682251 / 31250000) (469832033 / 1000000000) (Real.log (24995710453 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24995710453 / 15625000000) = -Real.log (15625000000 / 24995710453) := by
    rw [show ((24995710453 / 15625000000) : ℝ) = ((15625000000 / 24995710453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0398

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0399
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

theorem reflection_log_1_neg : (50116621 / 250000000) ≤ -Real.log (10240 / 12513) ∧
    -Real.log (10240 / 12513) ≤ (40093297 / 200000000) := by
  have h := checkLog_sound (w := (2273 / 22753)) (n := 12)
    (lo := (50116621 / 250000000)) (hi := (40093297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12513 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12513 / 10240) = 1/(10240 / 12513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50116621 / 250000000) (40093297 / 200000000) (Real.log (12513 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12513 / 10240) = -Real.log (10240 / 12513) := by
    rw [show ((12513 / 10240) : ℝ) = ((10240 / 12513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (250993609 / 1000000000) ≤ -Real.log (7967 / 10240) ∧
    -Real.log (7967 / 10240) ≤ (25099361 / 100000000) := by
  have h := checkLog_sound (w := (2273 / 18207)) (n := 12)
    (lo := (250993609 / 1000000000)) (hi := (25099361 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7967) = 1/(7967 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-25099361 / 100000000) (-250993609 / 1000000000) (Real.log (7967 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12514169 / 62500000) ≤ -Real.log (1024 / 1251) ∧
    -Real.log (1024 / 1251) ≤ (40045341 / 200000000) := by
  have h := checkLog_sound (w := (227 / 2275)) (n := 12)
    (lo := (12514169 / 62500000)) (hi := (40045341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251 / 1024) = 1/(1024 / 1251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12514169 / 62500000) (40045341 / 200000000) (Real.log (1251 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1251 / 1024) = -Real.log (1024 / 1251) := by
    rw [show ((1251 / 1024) : ℝ) = ((1024 / 1251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (125308563 / 500000000) ≤ -Real.log (797 / 1024) ∧
    -Real.log (797 / 1024) ≤ (250617127 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1821)) (n := 12)
    (lo := (125308563 / 500000000)) (hi := (250617127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 797) = 1/(797 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-250617127 / 1000000000) (-125308563 / 500000000) (Real.log (797 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (367379167 / 1000000000) ≤ -Real.log (5120 / 7393) ∧
    -Real.log (5120 / 7393) ≤ (11480599 / 31250000) := by
  have h := checkLog_sound (w := (2273 / 12513)) (n := 12)
    (lo := (367379167 / 1000000000)) (hi := (11480599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7393 / 5120) = 1/(5120 / 7393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (367379167 / 1000000000) (11480599 / 31250000) (Real.log (7393 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7393 / 5120) = -Real.log (5120 / 7393) := by
    rw [show ((7393 / 5120) : ℝ) = ((5120 / 7393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58688863 / 100000000) ≤ -Real.log (2847 / 5120) ∧
    -Real.log (2847 / 5120) ≤ (586888631 / 1000000000) := by
  have h := checkLog_sound (w := (2273 / 7967)) (n := 12)
    (lo := (58688863 / 100000000)) (hi := (586888631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2847) = 1/(2847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-586888631 / 1000000000) (-58688863 / 100000000) (Real.log (2847 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (73394659 / 200000000) ≤ -Real.log (512 / 739) ∧
    -Real.log (512 / 739) ≤ (22935831 / 62500000) := by
  have h := checkLog_sound (w := (227 / 1251)) (n := 12)
    (lo := (73394659 / 200000000)) (hi := (22935831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739 / 512) = 1/(512 / 739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (73394659 / 200000000) (22935831 / 62500000) (Real.log (739 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (739 / 512) = -Real.log (512 / 739) := by
    rw [show ((739 / 512) : ℝ) = ((512 / 739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (146458861 / 250000000) ≤ -Real.log (285 / 512) ∧
    -Real.log (285 / 512) ≤ (117167089 / 200000000) := by
  have h := checkLog_sound (w := (227 / 797)) (n := 12)
    (lo := (146458861 / 250000000)) (hi := (117167089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 285) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 285) = 1/(285 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-117167089 / 200000000) (-146458861 / 250000000) (Real.log (285 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (274827809 / 1000000000) ≤ -Real.log (62500 / 82269) ∧
    -Real.log (62500 / 82269) ≤ (27482781 / 100000000) := by
  have h := checkLog_sound (w := (19769 / 144769)) (n := 12)
    (lo := (274827809 / 1000000000)) (hi := (27482781 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82269 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82269 / 62500) = 1/(62500 / 82269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (274827809 / 1000000000) (27482781 / 100000000) (Real.log (82269 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (82269 / 62500) = -Real.log (62500 / 82269) := by
    rw [show ((82269 / 62500) : ℝ) = ((62500 / 82269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23765119 / 62500000) ≤ -Real.log (42731 / 62500) ∧
    -Real.log (42731 / 62500) ≤ (76048381 / 200000000) := by
  have h := checkLog_sound (w := (19769 / 105231)) (n := 12)
    (lo := (23765119 / 62500000)) (hi := (76048381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42731) = 1/(42731 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76048381 / 200000000) (-23765119 / 62500000) (Real.log (42731 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (275152149 / 1000000000) ≤ -Real.log (1000000 / 1316731) ∧
    -Real.log (1000000 / 1316731) ≤ (5503043 / 20000000) := by
  have h := checkLog_sound (w := (316731 / 2316731)) (n := 12)
    (lo := (275152149 / 1000000000)) (hi := (5503043 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1316731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1316731 / 1000000) = 1/(1000000 / 1316731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (275152149 / 1000000000) (5503043 / 20000000) (Real.log (1316731 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1316731 / 1000000) = -Real.log (1000000 / 1316731) := by
    rw [show ((1316731 / 1000000) : ℝ) = ((1000000 / 1316731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (190433323 / 500000000) ≤ -Real.log (683269 / 1000000) ∧
    -Real.log (683269 / 1000000) ≤ (380866647 / 1000000000) := by
  have h := checkLog_sound (w := (316731 / 1683269)) (n := 12)
    (lo := (190433323 / 500000000)) (hi := (380866647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 683269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 683269) = 1/(683269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-380866647 / 1000000000) (-190433323 / 500000000) (Real.log (683269 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51759843 / 250000000) ≤ -Real.log (1000000 / 1230031) ∧
    -Real.log (1000000 / 1230031) ≤ (207039373 / 1000000000) := by
  have h := checkLog_sound (w := (230031 / 2230031)) (n := 12)
    (lo := (51759843 / 250000000)) (hi := (207039373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230031 / 1000000) = 1/(1000000 / 1230031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51759843 / 250000000) (207039373 / 1000000000) (Real.log (1230031 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1230031 / 1000000) = -Real.log (1000000 / 1230031) := by
    rw [show ((1230031 / 1000000) : ℝ) = ((1000000 / 1230031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8168907 / 31250000) ≤ -Real.log (769969 / 1000000) ∧
    -Real.log (769969 / 1000000) ≤ (10456201 / 40000000) := by
  have h := checkLog_sound (w := (230031 / 1769969)) (n := 12)
    (lo := (8168907 / 31250000)) (hi := (10456201 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769969) = 1/(769969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10456201 / 40000000) (-8168907 / 31250000) (Real.log (769969 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (207306809 / 1000000000) ≤ -Real.log (25000 / 30759) ∧
    -Real.log (25000 / 30759) ≤ (20730681 / 100000000) := by
  have h := checkLog_sound (w := (5759 / 55759)) (n := 12)
    (lo := (207306809 / 1000000000)) (hi := (20730681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30759 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30759 / 25000) = 1/(25000 / 30759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (207306809 / 1000000000) (20730681 / 100000000) (Real.log (30759 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30759 / 25000) = -Real.log (25000 / 30759) := by
    rw [show ((30759 / 25000) : ℝ) = ((25000 / 30759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (52366481 / 200000000) ≤ -Real.log (19241 / 25000) ∧
    -Real.log (19241 / 25000) ≤ (130916203 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 44241)) (n := 12)
    (lo := (52366481 / 200000000)) (hi := (130916203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19241) = 1/(19241 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-130916203 / 500000000) (-52366481 / 200000000) (Real.log (19241 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (655069713 / 1000000000) ≤ -Real.log (500000000000 / 962638365589) ∧
    -Real.log (500000000000 / 962638365589) ≤ (327534857 / 500000000) := by
  have h := checkLog_sound (w := (462638365589 / 1462638365589)) (n := 12)
    (lo := (655069713 / 1000000000)) (hi := (327534857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((962638365589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(962638365589 / 500000000000) = 1/(500000000000 / 962638365589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (655069713 / 1000000000) (327534857 / 500000000) (Real.log (962638365589 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (962638365589 / 500000000000) = -Real.log (500000000000 / 962638365589) := by
    rw [show ((962638365589 / 500000000000) : ℝ) = ((500000000000 / 962638365589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (164004699 / 250000000) ≤ -Real.log (500000000000 / 963552422253) ∧
    -Real.log (500000000000 / 963552422253) ≤ (656018797 / 1000000000) := by
  have h := checkLog_sound (w := (463552422253 / 1463552422253)) (n := 12)
    (lo := (164004699 / 250000000)) (hi := (656018797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963552422253 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963552422253 / 500000000000) = 1/(500000000000 / 963552422253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (164004699 / 250000000) (656018797 / 1000000000) (Real.log (963552422253 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (963552422253 / 500000000000) = -Real.log (500000000000 / 963552422253) := by
    rw [show ((963552422253 / 500000000000) : ℝ) = ((500000000000 / 963552422253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (468444397 / 1000000000) ≤ -Real.log (500000000000 / 798753586183) ∧
    -Real.log (500000000000 / 798753586183) ≤ (234222199 / 500000000) := by
  have h := checkLog_sound (w := (298753586183 / 1298753586183)) (n := 12)
    (lo := (468444397 / 1000000000)) (hi := (234222199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798753586183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798753586183 / 500000000000) = 1/(500000000000 / 798753586183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (468444397 / 1000000000) (234222199 / 500000000) (Real.log (798753586183 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (798753586183 / 500000000000) = -Real.log (500000000000 / 798753586183) := by
    rw [show ((798753586183 / 500000000000) : ℝ) = ((500000000000 / 798753586183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (93827843 / 200000000) ≤ -Real.log (62500000000 / 99913595967) ∧
    -Real.log (62500000000 / 99913595967) ≤ (29321201 / 62500000) := by
  have h := checkLog_sound (w := (37413595967 / 162413595967)) (n := 12)
    (lo := (93827843 / 200000000)) (hi := (29321201 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99913595967 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99913595967 / 62500000000) = 1/(62500000000 / 99913595967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (93827843 / 200000000) (29321201 / 62500000) (Real.log (99913595967 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (99913595967 / 62500000000) = -Real.log (62500000000 / 99913595967) := by
    rw [show ((99913595967 / 62500000000) : ℝ) = ((62500000000 / 99913595967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0399

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0400Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0400
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

theorem reflection_log_1_neg : (12514169 / 62500000) ≤ -Real.log (1024 / 1251) ∧
    -Real.log (1024 / 1251) ≤ (40045341 / 200000000) := by
  have h := checkLog_sound (w := (227 / 2275)) (n := 12)
    (lo := (12514169 / 62500000)) (hi := (40045341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251 / 1024) = 1/(1024 / 1251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12514169 / 62500000) (40045341 / 200000000) (Real.log (1251 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1251 / 1024) = -Real.log (1024 / 1251) := by
    rw [show ((1251 / 1024) : ℝ) = ((1024 / 1251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (125308563 / 500000000) ≤ -Real.log (797 / 1024) ∧
    -Real.log (797 / 1024) ≤ (250617127 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1821)) (n := 12)
    (lo := (125308563 / 500000000)) (hi := (250617127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 797) = 1/(797 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-250617127 / 1000000000) (-125308563 / 500000000) (Real.log (797 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199986867 / 1000000000) ≤ -Real.log (10240 / 12507) ∧
    -Real.log (10240 / 12507) ≤ (49996717 / 250000000) := by
  have h := checkLog_sound (w := (2267 / 22747)) (n := 12)
    (lo := (199986867 / 1000000000)) (hi := (49996717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12507 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12507 / 10240) = 1/(10240 / 12507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199986867 / 1000000000) (49996717 / 250000000) (Real.log (12507 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12507 / 10240) = -Real.log (10240 / 12507) := by
    rw [show ((12507 / 10240) : ℝ) = ((10240 / 12507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (125120393 / 500000000) ≤ -Real.log (7973 / 10240) ∧
    -Real.log (7973 / 10240) ≤ (250240787 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 18213)) (n := 12)
    (lo := (125120393 / 500000000)) (hi := (250240787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7973) = 1/(7973 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-250240787 / 1000000000) (-125120393 / 500000000) (Real.log (7973 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (73394659 / 200000000) ≤ -Real.log (512 / 739) ∧
    -Real.log (512 / 739) ≤ (22935831 / 62500000) := by
  have h := checkLog_sound (w := (227 / 1251)) (n := 12)
    (lo := (73394659 / 200000000)) (hi := (22935831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739 / 512) = 1/(512 / 739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (73394659 / 200000000) (22935831 / 62500000) (Real.log (739 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (739 / 512) = -Real.log (512 / 739) := by
    rw [show ((739 / 512) : ℝ) = ((512 / 739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (146458861 / 250000000) ≤ -Real.log (285 / 512) ∧
    -Real.log (285 / 512) ≤ (117167089 / 200000000) := by
  have h := checkLog_sound (w := (227 / 797)) (n := 12)
    (lo := (146458861 / 250000000)) (hi := (117167089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 285) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 285) = 1/(285 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-117167089 / 200000000) (-146458861 / 250000000) (Real.log (285 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (366567259 / 1000000000) ≤ -Real.log (5120 / 7387) ∧
    -Real.log (5120 / 7387) ≤ (18328363 / 50000000) := by
  have h := checkLog_sound (w := (2267 / 12507)) (n := 12)
    (lo := (366567259 / 1000000000)) (hi := (18328363 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7387 / 5120) = 1/(5120 / 7387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (366567259 / 1000000000) (18328363 / 50000000) (Real.log (7387 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7387 / 5120) = -Real.log (5120 / 7387) := by
    rw [show ((7387 / 5120) : ℝ) = ((5120 / 7387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (292391683 / 500000000) ≤ -Real.log (2853 / 5120) ∧
    -Real.log (2853 / 5120) ≤ (584783367 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 7973)) (n := 12)
    (lo := (292391683 / 500000000)) (hi := (584783367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2853) = 1/(2853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-584783367 / 1000000000) (-292391683 / 500000000) (Real.log (2853 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (274504123 / 1000000000) ≤ -Real.log (500000 / 657939) ∧
    -Real.log (500000 / 657939) ≤ (68626031 / 250000000) := by
  have h := checkLog_sound (w := (157939 / 1157939)) (n := 12)
    (lo := (274504123 / 1000000000)) (hi := (68626031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657939 / 500000) = 1/(500000 / 657939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (274504123 / 1000000000) (68626031 / 250000000) (Real.log (657939 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (657939 / 500000) = -Real.log (500000 / 657939) := by
    rw [show ((657939 / 500000) : ℝ) = ((500000 / 657939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (189809507 / 500000000) ≤ -Real.log (342061 / 500000) ∧
    -Real.log (342061 / 500000) ≤ (75923803 / 200000000) := by
  have h := checkLog_sound (w := (157939 / 842061)) (n := 12)
    (lo := (189809507 / 500000000)) (hi := (75923803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342061) = 1/(342061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-75923803 / 200000000) (-189809507 / 500000000) (Real.log (342061 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34353571 / 125000000) ≤ -Real.log (200000 / 263261) ∧
    -Real.log (200000 / 263261) ≤ (274828569 / 1000000000) := by
  have h := checkLog_sound (w := (63261 / 463261)) (n := 12)
    (lo := (34353571 / 125000000)) (hi := (274828569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263261 / 200000) = 1/(200000 / 263261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34353571 / 125000000) (274828569 / 1000000000) (Real.log (263261 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (263261 / 200000) = -Real.log (200000 / 263261) := by
    rw [show ((263261 / 200000) : ℝ) = ((200000 / 263261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (380243367 / 1000000000) ≤ -Real.log (136739 / 200000) ∧
    -Real.log (136739 / 200000) ≤ (47530421 / 125000000) := by
  have h := checkLog_sound (w := (63261 / 336739)) (n := 12)
    (lo := (380243367 / 1000000000)) (hi := (47530421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 136739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 136739) = 1/(136739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-47530421 / 125000000) (-380243367 / 1000000000) (Real.log (136739 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20677349 / 100000000) ≤ -Real.log (125000 / 153713) ∧
    -Real.log (125000 / 153713) ≤ (206773491 / 1000000000) := by
  have h := checkLog_sound (w := (28713 / 278713)) (n := 12)
    (lo := (20677349 / 100000000)) (hi := (206773491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153713 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153713 / 125000) = 1/(125000 / 153713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20677349 / 100000000) (206773491 / 1000000000) (Real.log (153713 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (153713 / 125000) = -Real.log (125000 / 153713) := by
    rw [show ((153713 / 125000) : ℝ) = ((125000 / 153713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (130490211 / 500000000) ≤ -Real.log (96287 / 125000) ∧
    -Real.log (96287 / 125000) ≤ (260980423 / 1000000000) := by
  have h := checkLog_sound (w := (28713 / 221287)) (n := 12)
    (lo := (130490211 / 500000000)) (hi := (260980423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96287) = 1/(96287 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-260980423 / 1000000000) (-130490211 / 500000000) (Real.log (96287 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (41408037 / 200000000) ≤ -Real.log (62500 / 76877) ∧
    -Real.log (62500 / 76877) ≤ (103520093 / 500000000) := by
  have h := checkLog_sound (w := (14377 / 139377)) (n := 12)
    (lo := (41408037 / 200000000)) (hi := (103520093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76877 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76877 / 62500) = 1/(62500 / 76877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (41408037 / 200000000) (103520093 / 500000000) (Real.log (76877 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (76877 / 62500) = -Real.log (62500 / 76877) := by
    rw [show ((76877 / 62500) : ℝ) = ((62500 / 76877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (261406323 / 1000000000) ≤ -Real.log (48123 / 62500) ∧
    -Real.log (48123 / 62500) ≤ (65351581 / 250000000) := by
  have h := checkLog_sound (w := (14377 / 110623)) (n := 12)
    (lo := (261406323 / 1000000000)) (hi := (65351581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48123) = 1/(48123 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-65351581 / 250000000) (-261406323 / 1000000000) (Real.log (48123 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (327061569 / 500000000) ≤ -Real.log (2500000000 / 4808637933) ∧
    -Real.log (2500000000 / 4808637933) ≤ (654123139 / 1000000000) := by
  have h := checkLog_sound (w := (2308637933 / 7308637933)) (n := 12)
    (lo := (327061569 / 500000000)) (hi := (654123139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4808637933 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4808637933 / 2500000000) = 1/(2500000000 / 4808637933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (327061569 / 500000000) (654123139 / 1000000000) (Real.log (4808637933 / 2500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4808637933 / 2500000000) = -Real.log (2500000000 / 4808637933) := by
    rw [show ((4808637933 / 2500000000) : ℝ) = ((2500000000 / 4808637933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (10235499 / 15625000) ≤ -Real.log (62500000000 / 120330063113) ∧
    -Real.log (62500000000 / 120330063113) ≤ (655071937 / 1000000000) := by
  have h := checkLog_sound (w := (57830063113 / 182830063113)) (n := 12)
    (lo := (10235499 / 15625000)) (hi := (655071937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120330063113 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120330063113 / 62500000000) = 1/(62500000000 / 120330063113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (10235499 / 15625000) (655071937 / 1000000000) (Real.log (120330063113 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (120330063113 / 62500000000) = -Real.log (62500000000 / 120330063113) := by
    rw [show ((120330063113 / 62500000000) : ℝ) = ((62500000000 / 120330063113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (58469239 / 125000000) ≤ -Real.log (125000000000 / 199550562381) ∧
    -Real.log (125000000000 / 199550562381) ≤ (467753913 / 1000000000) := by
  have h := checkLog_sound (w := (74550562381 / 324550562381)) (n := 12)
    (lo := (58469239 / 125000000)) (hi := (467753913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199550562381 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199550562381 / 125000000000) = 1/(125000000000 / 199550562381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (58469239 / 125000000) (467753913 / 1000000000) (Real.log (199550562381 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (199550562381 / 125000000000) = -Real.log (125000000000 / 199550562381) := by
    rw [show ((199550562381 / 125000000000) : ℝ) = ((125000000000 / 199550562381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (117111627 / 250000000) ≤ -Real.log (500000000000 / 798755272947) ∧
    -Real.log (500000000000 / 798755272947) ≤ (468446509 / 1000000000) := by
  have h := checkLog_sound (w := (298755272947 / 1298755272947)) (n := 12)
    (lo := (117111627 / 250000000)) (hi := (468446509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798755272947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798755272947 / 500000000000) = 1/(500000000000 / 798755272947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (117111627 / 250000000) (468446509 / 1000000000) (Real.log (798755272947 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (798755272947 / 500000000000) = -Real.log (500000000000 / 798755272947) := by
    rw [show ((798755272947 / 500000000000) : ℝ) = ((500000000000 / 798755272947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0400

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0401Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0401
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

theorem reflection_log_1_neg : (199986867 / 1000000000) ≤ -Real.log (10240 / 12507) ∧
    -Real.log (10240 / 12507) ≤ (49996717 / 250000000) := by
  have h := checkLog_sound (w := (2267 / 22747)) (n := 12)
    (lo := (199986867 / 1000000000)) (hi := (49996717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12507 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12507 / 10240) = 1/(10240 / 12507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199986867 / 1000000000) (49996717 / 250000000) (Real.log (12507 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12507 / 10240) = -Real.log (10240 / 12507) := by
    rw [show ((12507 / 10240) : ℝ) = ((10240 / 12507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (125120393 / 500000000) ≤ -Real.log (7973 / 10240) ∧
    -Real.log (7973 / 10240) ≤ (250240787 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 18213)) (n := 12)
    (lo := (125120393 / 500000000)) (hi := (250240787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7973) = 1/(7973 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-250240787 / 1000000000) (-125120393 / 500000000) (Real.log (7973 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199746973 / 1000000000) ≤ -Real.log (1280 / 1563) ∧
    -Real.log (1280 / 1563) ≤ (99873487 / 500000000) := by
  have h := checkLog_sound (w := (283 / 2843)) (n := 12)
    (lo := (199746973 / 1000000000)) (hi := (99873487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563 / 1280) = 1/(1280 / 1563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199746973 / 1000000000) (99873487 / 500000000) (Real.log (1563 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1563 / 1280) = -Real.log (1280 / 1563) := by
    rw [show ((1563 / 1280) : ℝ) = ((1280 / 1563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (124932293 / 500000000) ≤ -Real.log (997 / 1280) ∧
    -Real.log (997 / 1280) ≤ (249864587 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2277)) (n := 12)
    (lo := (124932293 / 500000000)) (hi := (249864587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 997) = 1/(997 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-249864587 / 1000000000) (-124932293 / 500000000) (Real.log (997 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (366567259 / 1000000000) ≤ -Real.log (5120 / 7387) ∧
    -Real.log (5120 / 7387) ≤ (18328363 / 50000000) := by
  have h := checkLog_sound (w := (2267 / 12507)) (n := 12)
    (lo := (366567259 / 1000000000)) (hi := (18328363 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7387 / 5120) = 1/(5120 / 7387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (366567259 / 1000000000) (18328363 / 50000000) (Real.log (7387 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7387 / 5120) = -Real.log (5120 / 7387) := by
    rw [show ((7387 / 5120) : ℝ) = ((5120 / 7387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (292391683 / 500000000) ≤ -Real.log (2853 / 5120) ∧
    -Real.log (2853 / 5120) ≤ (584783367 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 7973)) (n := 12)
    (lo := (292391683 / 500000000)) (hi := (584783367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2853) = 1/(2853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-584783367 / 1000000000) (-292391683 / 500000000) (Real.log (2853 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (183080529 / 500000000) ≤ -Real.log (640 / 923) ∧
    -Real.log (640 / 923) ≤ (366161059 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1563)) (n := 12)
    (lo := (183080529 / 500000000)) (hi := (366161059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923 / 640) = 1/(640 / 923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (183080529 / 500000000) (366161059 / 1000000000) (Real.log (923 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (923 / 640) = -Real.log (640 / 923) := by
    rw [show ((923 / 640) : ℝ) = ((640 / 923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (291866197 / 500000000) ≤ -Real.log (357 / 640) ∧
    -Real.log (357 / 640) ≤ (116746479 / 200000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 357) = 1/(357 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-116746479 / 200000000) (-291866197 / 500000000) (Real.log (357 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68545083 / 250000000) ≤ -Real.log (250000 / 328863) ∧
    -Real.log (250000 / 328863) ≤ (274180333 / 1000000000) := by
  have h := checkLog_sound (w := (78863 / 578863)) (n := 12)
    (lo := (68545083 / 250000000)) (hi := (274180333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328863 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328863 / 250000) = 1/(250000 / 328863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68545083 / 250000000) (274180333 / 1000000000) (Real.log (328863 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (328863 / 250000) = -Real.log (250000 / 328863) := by
    rw [show ((328863 / 250000) : ℝ) = ((250000 / 328863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11843641 / 31250000) ≤ -Real.log (171137 / 250000) ∧
    -Real.log (171137 / 250000) ≤ (378996513 / 1000000000) := by
  have h := checkLog_sound (w := (78863 / 421137)) (n := 12)
    (lo := (11843641 / 31250000)) (hi := (378996513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171137) = 1/(171137 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-378996513 / 1000000000) (-11843641 / 31250000) (Real.log (171137 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (274504883 / 1000000000) ≤ -Real.log (1000000 / 1315879) ∧
    -Real.log (1000000 / 1315879) ≤ (68626221 / 250000000) := by
  have h := checkLog_sound (w := (315879 / 2315879)) (n := 12)
    (lo := (274504883 / 1000000000)) (hi := (68626221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315879 / 1000000) = 1/(1000000 / 1315879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (274504883 / 1000000000) (68626221 / 250000000) (Real.log (1315879 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1315879 / 1000000) = -Real.log (1000000 / 1315879) := by
    rw [show ((1315879 / 1000000) : ℝ) = ((1000000 / 1315879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94905119 / 250000000) ≤ -Real.log (684121 / 1000000) ∧
    -Real.log (684121 / 1000000) ≤ (379620477 / 1000000000) := by
  have h := checkLog_sound (w := (315879 / 1684121)) (n := 12)
    (lo := (94905119 / 250000000)) (hi := (379620477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684121) = 1/(684121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-379620477 / 1000000000) (-94905119 / 250000000) (Real.log (684121 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (206506723 / 1000000000) ≤ -Real.log (15625 / 19209) ∧
    -Real.log (15625 / 19209) ≤ (51626681 / 250000000) := by
  have h := checkLog_sound (w := (1792 / 17417)) (n := 12)
    (lo := (206506723 / 1000000000)) (hi := (51626681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19209 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19209 / 15625) = 1/(15625 / 19209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (206506723 / 1000000000) (51626681 / 250000000) (Real.log (19209 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19209 / 15625) = -Real.log (15625 / 19209) := by
    rw [show ((19209 / 15625) : ℝ) = ((15625 / 19209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (130277351 / 500000000) ≤ -Real.log (12041 / 15625) ∧
    -Real.log (12041 / 15625) ≤ (260554703 / 1000000000) := by
  have h := checkLog_sound (w := (1792 / 13833)) (n := 12)
    (lo := (130277351 / 500000000)) (hi := (260554703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12041) = 1/(12041 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-260554703 / 1000000000) (-130277351 / 500000000) (Real.log (12041 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (206774303 / 1000000000) ≤ -Real.log (200000 / 245941) ∧
    -Real.log (200000 / 245941) ≤ (6461697 / 31250000) := by
  have h := checkLog_sound (w := (45941 / 445941)) (n := 12)
    (lo := (206774303 / 1000000000)) (hi := (6461697 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245941 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245941 / 200000) = 1/(200000 / 245941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206774303 / 1000000000) (6461697 / 31250000) (Real.log (245941 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (245941 / 200000) = -Real.log (200000 / 245941) := by
    rw [show ((245941 / 200000) : ℝ) = ((200000 / 245941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6524543 / 25000000) ≤ -Real.log (154059 / 200000) ∧
    -Real.log (154059 / 200000) ≤ (260981721 / 1000000000) := by
  have h := checkLog_sound (w := (45941 / 354059)) (n := 12)
    (lo := (6524543 / 25000000)) (hi := (260981721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154059) = 1/(154059 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260981721 / 1000000000) (-6524543 / 25000000) (Real.log (154059 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (130635369 / 200000000) ≤ -Real.log (500000000000 / 960817941181) ∧
    -Real.log (500000000000 / 960817941181) ≤ (326588423 / 500000000) := by
  have h := checkLog_sound (w := (460817941181 / 1460817941181)) (n := 12)
    (lo := (130635369 / 200000000)) (hi := (326588423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960817941181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960817941181 / 500000000000) = 1/(500000000000 / 960817941181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (130635369 / 200000000) (326588423 / 500000000) (Real.log (960817941181 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (960817941181 / 500000000000) = -Real.log (500000000000 / 960817941181) := by
    rw [show ((960817941181 / 500000000000) : ℝ) = ((500000000000 / 960817941181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (654125359 / 1000000000) ≤ -Real.log (500000000000 / 961729723251) ∧
    -Real.log (500000000000 / 961729723251) ≤ (8176567 / 12500000) := by
  have h := checkLog_sound (w := (461729723251 / 1461729723251)) (n := 12)
    (lo := (654125359 / 1000000000)) (hi := (8176567 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961729723251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961729723251 / 500000000000) = 1/(500000000000 / 961729723251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (654125359 / 1000000000) (8176567 / 12500000) (Real.log (961729723251 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (961729723251 / 500000000000) = -Real.log (500000000000 / 961729723251) := by
    rw [show ((961729723251 / 500000000000) : ℝ) = ((500000000000 / 961729723251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (233530713 / 500000000) ≤ -Real.log (500000000000 / 797649696869) ∧
    -Real.log (500000000000 / 797649696869) ≤ (467061427 / 1000000000) := by
  have h := checkLog_sound (w := (297649696869 / 1297649696869)) (n := 12)
    (lo := (233530713 / 500000000)) (hi := (467061427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797649696869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797649696869 / 500000000000) = 1/(500000000000 / 797649696869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (233530713 / 500000000) (467061427 / 1000000000) (Real.log (797649696869 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (797649696869 / 500000000000) = -Real.log (500000000000 / 797649696869) := by
    rw [show ((797649696869 / 500000000000) : ℝ) = ((500000000000 / 797649696869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (467756023 / 1000000000) ≤ -Real.log (500000000000 / 798203934857) ∧
    -Real.log (500000000000 / 798203934857) ≤ (58469503 / 125000000) := by
  have h := checkLog_sound (w := (298203934857 / 1298203934857)) (n := 12)
    (lo := (467756023 / 1000000000)) (hi := (58469503 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798203934857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798203934857 / 500000000000) = 1/(500000000000 / 798203934857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (467756023 / 1000000000) (58469503 / 125000000) (Real.log (798203934857 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (798203934857 / 500000000000) = -Real.log (500000000000 / 798203934857) := by
    rw [show ((798203934857 / 500000000000) : ℝ) = ((500000000000 / 798203934857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0401

end


