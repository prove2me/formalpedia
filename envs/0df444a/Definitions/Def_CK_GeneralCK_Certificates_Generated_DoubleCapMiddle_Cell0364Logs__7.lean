-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0364Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0364Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:15:58.522807+00:00
-- url     : https://prove2.me/theorems/ee1e6fcd-3f87-4a04-84aa-595313a64659
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0364Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0365Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0364Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0365Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0366Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0367Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0368Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0369Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0370Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0364Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0365Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0366Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0367Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0368Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0369Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0370Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0364Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0365Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0366Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0367Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0368Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0369Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0370Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0364Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0365Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0366Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0367Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0368Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0369Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0370Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0364Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0364
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

theorem reflection_log_1_neg : (104411373 / 500000000) ≤ -Real.log (5120 / 6309) ∧
    -Real.log (5120 / 6309) ≤ (208822747 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 11429)) (n := 12)
    (lo := (104411373 / 500000000)) (hi := (208822747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6309 / 5120) = 1/(5120 / 6309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104411373 / 500000000) (208822747 / 1000000000) (Real.log (6309 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6309 / 5120) = -Real.log (5120 / 6309) := by
    rw [show ((6309 / 5120) : ℝ) = ((5120 / 6309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16516287 / 62500000) ≤ -Real.log (3931 / 5120) ∧
    -Real.log (3931 / 5120) ≤ (264260593 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 9051)) (n := 12)
    (lo := (16516287 / 62500000)) (hi := (264260593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3931) = 1/(3931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-264260593 / 1000000000) (-16516287 / 62500000) (Real.log (3931 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104292481 / 500000000) ≤ -Real.log (2048 / 2523) ∧
    -Real.log (2048 / 2523) ≤ (208584963 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 4571)) (n := 12)
    (lo := (104292481 / 500000000)) (hi := (208584963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 2048) = 1/(2048 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104292481 / 500000000) (208584963 / 1000000000) (Real.log (2523 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2523 / 2048) = -Real.log (2048 / 2523) := by
    rw [show ((2523 / 2048) : ℝ) = ((2048 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (263879083 / 1000000000) ≤ -Real.log (1573 / 2048) ∧
    -Real.log (1573 / 2048) ≤ (65969771 / 250000000) := by
  have h := checkLog_sound (w := (475 / 3621)) (n := 12)
    (lo := (263879083 / 1000000000)) (hi := (65969771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1573) = 1/(1573 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65969771 / 250000000) (-263879083 / 1000000000) (Real.log (1573 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (381481879 / 1000000000) ≤ -Real.log (2560 / 3749) ∧
    -Real.log (2560 / 3749) ≤ (9537047 / 25000000) := by
  have h := checkLog_sound (w := (1189 / 6309)) (n := 12)
    (lo := (381481879 / 1000000000)) (hi := (9537047 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3749 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3749 / 2560) = 1/(2560 / 3749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (381481879 / 1000000000) (9537047 / 25000000) (Real.log (3749 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3749 / 2560) = -Real.log (2560 / 3749) := by
    rw [show ((3749 / 2560) : ℝ) = ((2560 / 3749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (624466857 / 1000000000) ≤ -Real.log (1371 / 2560) ∧
    -Real.log (1371 / 2560) ≤ (312233429 / 500000000) := by
  have h := checkLog_sound (w := (1189 / 3931)) (n := 12)
    (lo := (624466857 / 1000000000)) (hi := (312233429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1371) = 1/(1371 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-312233429 / 500000000) (-624466857 / 1000000000) (Real.log (1371 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (95270423 / 250000000) ≤ -Real.log (1024 / 1499) ∧
    -Real.log (1024 / 1499) ≤ (381081693 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 2523)) (n := 12)
    (lo := (95270423 / 250000000)) (hi := (381081693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1024) = 1/(1024 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (95270423 / 250000000) (381081693 / 1000000000) (Real.log (1499 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1499 / 1024) = -Real.log (1024 / 1499) := by
    rw [show ((1499 / 1024) : ℝ) = ((1024 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (155843341 / 250000000) ≤ -Real.log (549 / 1024) ∧
    -Real.log (549 / 1024) ≤ (124674673 / 200000000) := by
  have h := checkLog_sound (w := (475 / 1573)) (n := 12)
    (lo := (155843341 / 250000000)) (hi := (124674673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 549) = 1/(549 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-124674673 / 200000000) (-155843341 / 250000000) (Real.log (549 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (286111589 / 1000000000) ≤ -Real.log (1000000 / 1331241) ∧
    -Real.log (1000000 / 1331241) ≤ (28611159 / 100000000) := by
  have h := checkLog_sound (w := (331241 / 2331241)) (n := 12)
    (lo := (286111589 / 1000000000)) (hi := (28611159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331241 / 1000000) = 1/(1000000 / 1331241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (286111589 / 1000000000) (28611159 / 100000000) (Real.log (1331241 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1331241 / 1000000) = -Real.log (1000000 / 1331241) := by
    rw [show ((1331241 / 1000000) : ℝ) = ((1000000 / 1331241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (201165761 / 500000000) ≤ -Real.log (668759 / 1000000) ∧
    -Real.log (668759 / 1000000) ≤ (402331523 / 1000000000) := by
  have h := checkLog_sound (w := (331241 / 1668759)) (n := 12)
    (lo := (201165761 / 500000000)) (hi := (402331523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 668759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 668759) = 1/(668759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-402331523 / 1000000000) (-201165761 / 500000000) (Real.log (668759 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (286433793 / 1000000000) ≤ -Real.log (100000 / 133167) ∧
    -Real.log (100000 / 133167) ≤ (143216897 / 500000000) := by
  have h := checkLog_sound (w := (33167 / 233167)) (n := 12)
    (lo := (286433793 / 1000000000)) (hi := (143216897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133167 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133167 / 100000) = 1/(100000 / 133167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (286433793 / 1000000000) (143216897 / 500000000) (Real.log (133167 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (133167 / 100000) = -Real.log (100000 / 133167) := by
    rw [show ((133167 / 100000) : ℝ) = ((100000 / 133167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80594643 / 200000000) ≤ -Real.log (66833 / 100000) ∧
    -Real.log (66833 / 100000) ≤ (12592913 / 31250000) := by
  have h := checkLog_sound (w := (33167 / 166833)) (n := 12)
    (lo := (80594643 / 200000000)) (hi := (12592913 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66833) = 1/(66833 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12592913 / 31250000) (-80594643 / 200000000) (Real.log (66833 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108183521 / 500000000) ≤ -Real.log (500000 / 620779) ∧
    -Real.log (500000 / 620779) ≤ (216367043 / 1000000000) := by
  have h := checkLog_sound (w := (120779 / 1120779)) (n := 12)
    (lo := (108183521 / 500000000)) (hi := (216367043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620779 / 500000) = 1/(500000 / 620779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108183521 / 500000000) (216367043 / 1000000000) (Real.log (620779 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (620779 / 500000) = -Real.log (500000 / 620779) := by
    rw [show ((620779 / 500000) : ℝ) = ((500000 / 620779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (276488949 / 1000000000) ≤ -Real.log (379221 / 500000) ∧
    -Real.log (379221 / 500000) ≤ (5529779 / 20000000) := by
  have h := checkLog_sound (w := (120779 / 879221)) (n := 12)
    (lo := (276488949 / 1000000000)) (hi := (5529779 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379221) = 1/(379221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5529779 / 20000000) (-276488949 / 1000000000) (Real.log (379221 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (54158603 / 250000000) ≤ -Real.log (100000 / 124189) ∧
    -Real.log (100000 / 124189) ≤ (216634413 / 1000000000) := by
  have h := checkLog_sound (w := (24189 / 224189)) (n := 12)
    (lo := (54158603 / 250000000)) (hi := (216634413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124189 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124189 / 100000) = 1/(100000 / 124189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54158603 / 250000000) (216634413 / 1000000000) (Real.log (124189 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (124189 / 100000) = -Real.log (100000 / 124189) := by
    rw [show ((124189 / 100000) : ℝ) = ((100000 / 124189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55385357 / 200000000) ≤ -Real.log (75811 / 100000) ∧
    -Real.log (75811 / 100000) ≤ (138463393 / 500000000) := by
  have h := checkLog_sound (w := (24189 / 175811)) (n := 12)
    (lo := (55385357 / 200000000)) (hi := (138463393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75811) = 1/(75811 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-138463393 / 500000000) (-55385357 / 200000000) (Real.log (75811 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (86055389 / 125000000) ≤ -Real.log (250000000000 / 497653489523) ∧
    -Real.log (250000000000 / 497653489523) ≤ (688443113 / 1000000000) := by
  have h := checkLog_sound (w := (247653489523 / 747653489523)) (n := 12)
    (lo := (86055389 / 125000000)) (hi := (688443113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497653489523 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497653489523 / 250000000000) = 1/(250000000000 / 497653489523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (86055389 / 125000000) (688443113 / 1000000000) (Real.log (497653489523 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (497653489523 / 250000000000) = -Real.log (250000000000 / 497653489523) := by
    rw [show ((497653489523 / 250000000000) : ℝ) = ((250000000000 / 497653489523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (689407009 / 1000000000) ≤ -Real.log (500000000000 / 996266814299) ∧
    -Real.log (500000000000 / 996266814299) ≤ (68940701 / 100000000) := by
  have h := checkLog_sound (w := (496266814299 / 1496266814299)) (n := 12)
    (lo := (689407009 / 1000000000)) (hi := (68940701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996266814299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996266814299 / 500000000000) = 1/(500000000000 / 996266814299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (689407009 / 1000000000) (68940701 / 100000000) (Real.log (996266814299 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (996266814299 / 500000000000) = -Real.log (500000000000 / 996266814299) := by
    rw [show ((996266814299 / 500000000000) : ℝ) = ((500000000000 / 996266814299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (61606999 / 125000000) ≤ -Real.log (500000000000 / 818492383069) ∧
    -Real.log (500000000000 / 818492383069) ≤ (492855993 / 1000000000) := by
  have h := checkLog_sound (w := (318492383069 / 1318492383069)) (n := 12)
    (lo := (61606999 / 125000000)) (hi := (492855993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818492383069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818492383069 / 500000000000) = 1/(500000000000 / 818492383069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (61606999 / 125000000) (492855993 / 1000000000) (Real.log (818492383069 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (818492383069 / 500000000000) = -Real.log (500000000000 / 818492383069) := by
    rw [show ((818492383069 / 500000000000) : ℝ) = ((500000000000 / 818492383069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (493561197 / 1000000000) ≤ -Real.log (500000000000 / 819069791983) ∧
    -Real.log (500000000000 / 819069791983) ≤ (246780599 / 500000000) := by
  have h := checkLog_sound (w := (319069791983 / 1319069791983)) (n := 12)
    (lo := (493561197 / 1000000000)) (hi := (246780599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819069791983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819069791983 / 500000000000) = 1/(500000000000 / 819069791983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (493561197 / 1000000000) (246780599 / 500000000) (Real.log (819069791983 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (819069791983 / 500000000000) = -Real.log (500000000000 / 819069791983) := by
    rw [show ((819069791983 / 500000000000) : ℝ) = ((500000000000 / 819069791983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0364

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0365Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0365
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

theorem reflection_log_1_neg : (104292481 / 500000000) ≤ -Real.log (2048 / 2523) ∧
    -Real.log (2048 / 2523) ≤ (208584963 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 4571)) (n := 12)
    (lo := (104292481 / 500000000)) (hi := (208584963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 2048) = 1/(2048 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104292481 / 500000000) (208584963 / 1000000000) (Real.log (2523 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2523 / 2048) = -Real.log (2048 / 2523) := by
    rw [show ((2523 / 2048) : ℝ) = ((2048 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (263879083 / 1000000000) ≤ -Real.log (1573 / 2048) ∧
    -Real.log (1573 / 2048) ≤ (65969771 / 250000000) := by
  have h := checkLog_sound (w := (475 / 3621)) (n := 12)
    (lo := (263879083 / 1000000000)) (hi := (65969771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1573) = 1/(1573 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65969771 / 250000000) (-263879083 / 1000000000) (Real.log (1573 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104173561 / 500000000) ≤ -Real.log (2560 / 3153) ∧
    -Real.log (2560 / 3153) ≤ (208347123 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 5713)) (n := 12)
    (lo := (104173561 / 500000000)) (hi := (208347123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3153 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3153 / 2560) = 1/(2560 / 3153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104173561 / 500000000) (208347123 / 1000000000) (Real.log (3153 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3153 / 2560) = -Real.log (2560 / 3153) := by
    rw [show ((3153 / 2560) : ℝ) = ((2560 / 3153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (263497719 / 1000000000) ≤ -Real.log (1967 / 2560) ∧
    -Real.log (1967 / 2560) ≤ (6587443 / 25000000) := by
  have h := checkLog_sound (w := (593 / 4527)) (n := 12)
    (lo := (263497719 / 1000000000)) (hi := (6587443 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1967) = 1/(1967 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6587443 / 25000000) (-263497719 / 1000000000) (Real.log (1967 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (95270423 / 250000000) ≤ -Real.log (1024 / 1499) ∧
    -Real.log (1024 / 1499) ≤ (381081693 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 2523)) (n := 12)
    (lo := (95270423 / 250000000)) (hi := (381081693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1024) = 1/(1024 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (95270423 / 250000000) (381081693 / 1000000000) (Real.log (1499 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1499 / 1024) = -Real.log (1024 / 1499) := by
    rw [show ((1499 / 1024) : ℝ) = ((1024 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (155843341 / 250000000) ≤ -Real.log (549 / 1024) ∧
    -Real.log (549 / 1024) ≤ (124674673 / 200000000) := by
  have h := checkLog_sound (w := (475 / 1573)) (n := 12)
    (lo := (155843341 / 250000000)) (hi := (124674673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 549) = 1/(549 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-124674673 / 200000000) (-155843341 / 250000000) (Real.log (549 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (76136269 / 200000000) ≤ -Real.log (1280 / 1873) ∧
    -Real.log (1280 / 1873) ≤ (190340673 / 500000000) := by
  have h := checkLog_sound (w := (593 / 3153)) (n := 12)
    (lo := (76136269 / 200000000)) (hi := (190340673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1873 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1873 / 1280) = 1/(1280 / 1873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (76136269 / 200000000) (190340673 / 500000000) (Real.log (1873 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1873 / 1280) = -Real.log (1280 / 1873) := by
    rw [show ((1873 / 1280) : ℝ) = ((1280 / 1873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (77785133 / 125000000) ≤ -Real.log (687 / 1280) ∧
    -Real.log (687 / 1280) ≤ (124456213 / 200000000) := by
  have h := checkLog_sound (w := (593 / 1967)) (n := 12)
    (lo := (77785133 / 125000000)) (hi := (124456213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 687) = 1/(687 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-124456213 / 200000000) (-77785133 / 125000000) (Real.log (687 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57158157 / 200000000) ≤ -Real.log (500000 / 665407) ∧
    -Real.log (500000 / 665407) ≤ (142895393 / 500000000) := by
  have h := checkLog_sound (w := (165407 / 1165407)) (n := 12)
    (lo := (57158157 / 200000000)) (hi := (142895393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665407 / 500000) = 1/(500000 / 665407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57158157 / 200000000) (142895393 / 500000000) (Real.log (665407 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (665407 / 500000) = -Real.log (500000 / 665407) := by
    rw [show ((665407 / 500000) : ℝ) = ((500000 / 665407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40169323 / 100000000) ≤ -Real.log (334593 / 500000) ∧
    -Real.log (334593 / 500000) ≤ (401693231 / 1000000000) := by
  have h := checkLog_sound (w := (165407 / 834593)) (n := 12)
    (lo := (40169323 / 100000000)) (hi := (401693231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334593) = 1/(334593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-401693231 / 1000000000) (-40169323 / 100000000) (Real.log (334593 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (286112341 / 1000000000) ≤ -Real.log (500000 / 665621) ∧
    -Real.log (500000 / 665621) ≤ (143056171 / 500000000) := by
  have h := checkLog_sound (w := (165621 / 1165621)) (n := 12)
    (lo := (286112341 / 1000000000)) (hi := (143056171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665621 / 500000) = 1/(500000 / 665621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (286112341 / 1000000000) (143056171 / 500000000) (Real.log (665621 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (665621 / 500000) = -Real.log (500000 / 665621) := by
    rw [show ((665621 / 500000) : ℝ) = ((500000 / 665621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (201166509 / 500000000) ≤ -Real.log (334379 / 500000) ∧
    -Real.log (334379 / 500000) ≤ (402333019 / 1000000000) := by
  have h := checkLog_sound (w := (165621 / 834379)) (n := 12)
    (lo := (201166509 / 500000000)) (hi := (402333019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334379) = 1/(334379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-402333019 / 1000000000) (-201166509 / 500000000) (Real.log (334379 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108050203 / 500000000) ≤ -Real.log (1000000 / 1241227) ∧
    -Real.log (1000000 / 1241227) ≤ (216100407 / 1000000000) := by
  have h := checkLog_sound (w := (241227 / 2241227)) (n := 12)
    (lo := (108050203 / 500000000)) (hi := (216100407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241227 / 1000000) = 1/(1000000 / 1241227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108050203 / 500000000) (216100407 / 1000000000) (Real.log (1241227 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1241227 / 1000000) = -Real.log (1000000 / 1241227) := by
    rw [show ((1241227 / 1000000) : ℝ) = ((1000000 / 1241227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (17253289 / 62500000) ≤ -Real.log (758773 / 1000000) ∧
    -Real.log (758773 / 1000000) ≤ (2208421 / 8000000) := by
  have h := checkLog_sound (w := (241227 / 1758773)) (n := 12)
    (lo := (17253289 / 62500000)) (hi := (2208421 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758773) = 1/(758773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2208421 / 8000000) (-17253289 / 62500000) (Real.log (758773 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (216367847 / 1000000000) ≤ -Real.log (1000000 / 1241559) ∧
    -Real.log (1000000 / 1241559) ≤ (27045981 / 125000000) := by
  have h := checkLog_sound (w := (241559 / 2241559)) (n := 12)
    (lo := (216367847 / 1000000000)) (hi := (27045981 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241559 / 1000000) = 1/(1000000 / 1241559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (216367847 / 1000000000) (27045981 / 125000000) (Real.log (1241559 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1241559 / 1000000) = -Real.log (1000000 / 1241559) := by
    rw [show ((1241559 / 1000000) : ℝ) = ((1000000 / 1241559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (69122567 / 250000000) ≤ -Real.log (758441 / 1000000) ∧
    -Real.log (758441 / 1000000) ≤ (276490269 / 1000000000) := by
  have h := checkLog_sound (w := (241559 / 1758441)) (n := 12)
    (lo := (69122567 / 250000000)) (hi := (276490269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758441) = 1/(758441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-276490269 / 1000000000) (-69122567 / 250000000) (Real.log (758441 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (137496803 / 200000000) ≤ -Real.log (100000000000 / 198870568123) ∧
    -Real.log (100000000000 / 198870568123) ≤ (42967751 / 62500000) := by
  have h := checkLog_sound (w := (98870568123 / 298870568123)) (n := 12)
    (lo := (137496803 / 200000000)) (hi := (42967751 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198870568123 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198870568123 / 100000000000) = 1/(100000000000 / 198870568123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (137496803 / 200000000) (42967751 / 62500000) (Real.log (198870568123 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (198870568123 / 100000000000) = -Real.log (100000000000 / 198870568123) := by
    rw [show ((198870568123 / 100000000000) : ℝ) = ((100000000000 / 198870568123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (688445359 / 1000000000) ≤ -Real.log (500000000000 / 995309214993) ∧
    -Real.log (500000000000 / 995309214993) ≤ (8605567 / 12500000) := by
  have h := checkLog_sound (w := (495309214993 / 1495309214993)) (n := 12)
    (lo := (688445359 / 1000000000)) (hi := (8605567 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((995309214993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(995309214993 / 500000000000) = 1/(500000000000 / 995309214993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (688445359 / 1000000000) (8605567 / 12500000) (Real.log (995309214993 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (995309214993 / 500000000000) = -Real.log (500000000000 / 995309214993) := by
    rw [show ((995309214993 / 500000000000) : ℝ) = ((500000000000 / 995309214993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (49215303 / 100000000) ≤ -Real.log (500000000000 / 817917216347) ∧
    -Real.log (500000000000 / 817917216347) ≤ (492153031 / 1000000000) := by
  have h := checkLog_sound (w := (317917216347 / 1317917216347)) (n := 12)
    (lo := (49215303 / 100000000)) (hi := (492153031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817917216347 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817917216347 / 500000000000) = 1/(500000000000 / 817917216347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (49215303 / 100000000) (492153031 / 1000000000) (Real.log (817917216347 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (817917216347 / 500000000000) = -Real.log (500000000000 / 817917216347) := by
    rw [show ((817917216347 / 500000000000) : ℝ) = ((500000000000 / 817917216347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (123214529 / 250000000) ≤ -Real.log (250000000000 / 409247060747) ∧
    -Real.log (250000000000 / 409247060747) ≤ (492858117 / 1000000000) := by
  have h := checkLog_sound (w := (159247060747 / 659247060747)) (n := 12)
    (lo := (123214529 / 250000000)) (hi := (492858117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409247060747 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409247060747 / 250000000000) = 1/(250000000000 / 409247060747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (123214529 / 250000000) (492858117 / 1000000000) (Real.log (409247060747 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (409247060747 / 250000000000) = -Real.log (250000000000 / 409247060747) := by
    rw [show ((409247060747 / 250000000000) : ℝ) = ((250000000000 / 409247060747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0365

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0366Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0366
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

theorem reflection_log_1_neg : (104173561 / 500000000) ≤ -Real.log (2560 / 3153) ∧
    -Real.log (2560 / 3153) ≤ (208347123 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 5713)) (n := 12)
    (lo := (104173561 / 500000000)) (hi := (208347123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3153 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3153 / 2560) = 1/(2560 / 3153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104173561 / 500000000) (208347123 / 1000000000) (Real.log (3153 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3153 / 2560) = -Real.log (2560 / 3153) := by
    rw [show ((3153 / 2560) : ℝ) = ((2560 / 3153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (263497719 / 1000000000) ≤ -Real.log (1967 / 2560) ∧
    -Real.log (1967 / 2560) ≤ (6587443 / 25000000) := by
  have h := checkLog_sound (w := (593 / 4527)) (n := 12)
    (lo := (263497719 / 1000000000)) (hi := (6587443 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1967) = 1/(1967 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6587443 / 25000000) (-263497719 / 1000000000) (Real.log (1967 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8324369 / 40000000) ≤ -Real.log (10240 / 12609) ∧
    -Real.log (10240 / 12609) ≤ (104054613 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 22849)) (n := 12)
    (lo := (8324369 / 40000000)) (hi := (104054613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12609 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12609 / 10240) = 1/(10240 / 12609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8324369 / 40000000) (104054613 / 500000000) (Real.log (12609 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12609 / 10240) = -Real.log (10240 / 12609) := by
    rw [show ((12609 / 10240) : ℝ) = ((10240 / 12609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (526233 / 2000000) ≤ -Real.log (7871 / 10240) ∧
    -Real.log (7871 / 10240) ≤ (263116501 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 18111)) (n := 12)
    (lo := (526233 / 2000000)) (hi := (263116501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7871) = 1/(7871 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-263116501 / 1000000000) (-526233 / 2000000) (Real.log (7871 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (76136269 / 200000000) ≤ -Real.log (1280 / 1873) ∧
    -Real.log (1280 / 1873) ≤ (190340673 / 500000000) := by
  have h := checkLog_sound (w := (593 / 3153)) (n := 12)
    (lo := (76136269 / 200000000)) (hi := (190340673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1873 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1873 / 1280) = 1/(1280 / 1873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (76136269 / 200000000) (190340673 / 500000000) (Real.log (1873 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1873 / 1280) = -Real.log (1280 / 1873) := by
    rw [show ((1873 / 1280) : ℝ) = ((1280 / 1873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77785133 / 125000000) ≤ -Real.log (687 / 1280) ∧
    -Real.log (687 / 1280) ≤ (124456213 / 200000000) := by
  have h := checkLog_sound (w := (593 / 1967)) (n := 12)
    (lo := (77785133 / 125000000)) (hi := (124456213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 687) = 1/(687 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-124456213 / 200000000) (-77785133 / 125000000) (Real.log (687 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190140419 / 500000000) ≤ -Real.log (5120 / 7489) ∧
    -Real.log (5120 / 7489) ≤ (380280839 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 12609)) (n := 12)
    (lo := (190140419 / 500000000)) (hi := (380280839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7489 / 5120) = 1/(5120 / 7489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190140419 / 500000000) (380280839 / 1000000000) (Real.log (7489 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7489 / 5120) = -Real.log (5120 / 7489) := by
    rw [show ((7489 / 5120) : ℝ) = ((5120 / 7489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (621189957 / 1000000000) ≤ -Real.log (2751 / 5120) ∧
    -Real.log (2751 / 5120) ≤ (310594979 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 7871)) (n := 12)
    (lo := (621189957 / 1000000000)) (hi := (310594979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2751) = 1/(2751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-310594979 / 500000000) (-621189957 / 1000000000) (Real.log (2751 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2283753 / 8000000) ≤ -Real.log (500000 / 665193) ∧
    -Real.log (500000 / 665193) ≤ (142734563 / 500000000) := by
  have h := checkLog_sound (w := (165193 / 1165193)) (n := 12)
    (lo := (2283753 / 8000000)) (hi := (142734563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665193 / 500000) = 1/(500000 / 665193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2283753 / 8000000) (142734563 / 500000000) (Real.log (665193 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (665193 / 500000) = -Real.log (500000 / 665193) := by
    rw [show ((665193 / 500000) : ℝ) = ((500000 / 665193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100263463 / 250000000) ≤ -Real.log (334807 / 500000) ∧
    -Real.log (334807 / 500000) ≤ (401053853 / 1000000000) := by
  have h := checkLog_sound (w := (165193 / 834807)) (n := 12)
    (lo := (100263463 / 250000000)) (hi := (401053853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334807) = 1/(334807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-401053853 / 1000000000) (-100263463 / 250000000) (Real.log (334807 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17861971 / 62500000) ≤ -Real.log (200000 / 266163) ∧
    -Real.log (200000 / 266163) ≤ (285791537 / 1000000000) := by
  have h := checkLog_sound (w := (66163 / 466163)) (n := 12)
    (lo := (17861971 / 62500000)) (hi := (285791537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266163 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266163 / 200000) = 1/(200000 / 266163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17861971 / 62500000) (285791537 / 1000000000) (Real.log (266163 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (266163 / 200000) = -Real.log (200000 / 266163) := by
    rw [show ((266163 / 200000) : ℝ) = ((200000 / 266163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100423681 / 250000000) ≤ -Real.log (133837 / 200000) ∧
    -Real.log (133837 / 200000) ≤ (16067789 / 40000000) := by
  have h := checkLog_sound (w := (66163 / 333837)) (n := 12)
    (lo := (100423681 / 250000000)) (hi := (16067789 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133837) = 1/(133837 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16067789 / 40000000) (-100423681 / 250000000) (Real.log (133837 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (215833699 / 1000000000) ≤ -Real.log (15625 / 19389) ∧
    -Real.log (15625 / 19389) ≤ (2158337 / 10000000) := by
  have h := checkLog_sound (w := (1882 / 17507)) (n := 12)
    (lo := (215833699 / 1000000000)) (hi := (2158337 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19389 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19389 / 15625) = 1/(15625 / 19389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (215833699 / 1000000000) (2158337 / 10000000) (Real.log (19389 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19389 / 15625) = -Real.log (15625 / 19389) := by
    rw [show ((19389 / 15625) : ℝ) = ((15625 / 19389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (34452061 / 125000000) ≤ -Real.log (11861 / 15625) ∧
    -Real.log (11861 / 15625) ≤ (275616489 / 1000000000) := by
  have h := checkLog_sound (w := (1882 / 13743)) (n := 12)
    (lo := (34452061 / 125000000)) (hi := (275616489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11861) = 1/(11861 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-275616489 / 1000000000) (-34452061 / 125000000) (Real.log (11861 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (54025303 / 250000000) ≤ -Real.log (250000 / 310307) ∧
    -Real.log (250000 / 310307) ≤ (216101213 / 1000000000) := by
  have h := checkLog_sound (w := (60307 / 560307)) (n := 12)
    (lo := (54025303 / 250000000)) (hi := (216101213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310307 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310307 / 250000) = 1/(250000 / 310307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54025303 / 250000000) (216101213 / 1000000000) (Real.log (310307 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (310307 / 250000) = -Real.log (250000 / 310307) := by
    rw [show ((310307 / 250000) : ℝ) = ((250000 / 310307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276053941 / 1000000000) ≤ -Real.log (189693 / 250000) ∧
    -Real.log (189693 / 250000) ≤ (138026971 / 500000000) := by
  have h := checkLog_sound (w := (60307 / 439693)) (n := 12)
    (lo := (276053941 / 1000000000)) (hi := (138026971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189693) = 1/(189693 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-138026971 / 500000000) (-276053941 / 1000000000) (Real.log (189693 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (686522977 / 1000000000) ≤ -Real.log (500000000000 / 993397688817) ∧
    -Real.log (500000000000 / 993397688817) ≤ (343261489 / 500000000) := by
  have h := checkLog_sound (w := (493397688817 / 1493397688817)) (n := 12)
    (lo := (686522977 / 1000000000)) (hi := (343261489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993397688817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993397688817 / 500000000000) = 1/(500000000000 / 993397688817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (686522977 / 1000000000) (343261489 / 500000000) (Real.log (993397688817 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (993397688817 / 500000000000) = -Real.log (500000000000 / 993397688817) := by
    rw [show ((993397688817 / 500000000000) : ℝ) = ((500000000000 / 993397688817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (687486261 / 1000000000) ≤ -Real.log (50000000000 / 99435507371) ∧
    -Real.log (50000000000 / 99435507371) ≤ (343743131 / 500000000) := by
  have h := checkLog_sound (w := (49435507371 / 149435507371)) (n := 12)
    (lo := (687486261 / 1000000000)) (hi := (343743131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99435507371 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99435507371 / 50000000000) = 1/(50000000000 / 99435507371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (687486261 / 1000000000) (343743131 / 500000000) (Real.log (99435507371 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (99435507371 / 50000000000) = -Real.log (50000000000 / 99435507371) := by
    rw [show ((99435507371 / 50000000000) : ℝ) = ((50000000000 / 99435507371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (491450187 / 1000000000) ≤ -Real.log (250000000000 / 408671275609) ∧
    -Real.log (250000000000 / 408671275609) ≤ (122862547 / 250000000) := by
  have h := checkLog_sound (w := (158671275609 / 658671275609)) (n := 12)
    (lo := (491450187 / 1000000000)) (hi := (122862547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408671275609 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408671275609 / 250000000000) = 1/(250000000000 / 408671275609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (491450187 / 1000000000) (122862547 / 250000000) (Real.log (408671275609 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (408671275609 / 250000000000) = -Real.log (250000000000 / 408671275609) := by
    rw [show ((408671275609 / 250000000000) : ℝ) = ((250000000000 / 408671275609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (246077577 / 500000000) ≤ -Real.log (500000000000 / 817918953257) ∧
    -Real.log (500000000000 / 817918953257) ≤ (98431031 / 200000000) := by
  have h := checkLog_sound (w := (317918953257 / 1317918953257)) (n := 12)
    (lo := (246077577 / 500000000)) (hi := (98431031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817918953257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817918953257 / 500000000000) = 1/(500000000000 / 817918953257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (246077577 / 500000000) (98431031 / 200000000) (Real.log (817918953257 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (817918953257 / 500000000000) = -Real.log (500000000000 / 817918953257) := by
    rw [show ((817918953257 / 500000000000) : ℝ) = ((500000000000 / 817918953257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0366

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0367Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0367
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

theorem reflection_log_1_neg : (8324369 / 40000000) ≤ -Real.log (10240 / 12609) ∧
    -Real.log (10240 / 12609) ≤ (104054613 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 22849)) (n := 12)
    (lo := (8324369 / 40000000)) (hi := (104054613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12609 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12609 / 10240) = 1/(10240 / 12609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8324369 / 40000000) (104054613 / 500000000) (Real.log (12609 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12609 / 10240) = -Real.log (10240 / 12609) := by
    rw [show ((12609 / 10240) : ℝ) = ((10240 / 12609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (526233 / 2000000) ≤ -Real.log (7871 / 10240) ∧
    -Real.log (7871 / 10240) ≤ (263116501 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 18111)) (n := 12)
    (lo := (526233 / 2000000)) (hi := (263116501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7871) = 1/(7871 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-263116501 / 1000000000) (-526233 / 2000000) (Real.log (7871 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (207871271 / 1000000000) ≤ -Real.log (5120 / 6303) ∧
    -Real.log (5120 / 6303) ≤ (25983909 / 125000000) := by
  have h := checkLog_sound (w := (1183 / 11423)) (n := 12)
    (lo := (207871271 / 1000000000)) (hi := (25983909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6303 / 5120) = 1/(5120 / 6303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (207871271 / 1000000000) (25983909 / 125000000) (Real.log (6303 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6303 / 5120) = -Real.log (5120 / 6303) := by
    rw [show ((6303 / 5120) : ℝ) = ((5120 / 6303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (262735427 / 1000000000) ≤ -Real.log (3937 / 5120) ∧
    -Real.log (3937 / 5120) ≤ (65683857 / 250000000) := by
  have h := checkLog_sound (w := (1183 / 9057)) (n := 12)
    (lo := (262735427 / 1000000000)) (hi := (65683857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3937) = 1/(3937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65683857 / 250000000) (-262735427 / 1000000000) (Real.log (3937 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190140419 / 500000000) ≤ -Real.log (5120 / 7489) ∧
    -Real.log (5120 / 7489) ≤ (380280839 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 12609)) (n := 12)
    (lo := (190140419 / 500000000)) (hi := (380280839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7489 / 5120) = 1/(5120 / 7489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190140419 / 500000000) (380280839 / 1000000000) (Real.log (7489 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7489 / 5120) = -Real.log (5120 / 7489) := by
    rw [show ((7489 / 5120) : ℝ) = ((5120 / 7489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (621189957 / 1000000000) ≤ -Real.log (2751 / 5120) ∧
    -Real.log (2751 / 5120) ≤ (310594979 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 7871)) (n := 12)
    (lo := (621189957 / 1000000000)) (hi := (310594979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2751) = 1/(2751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-310594979 / 500000000) (-621189957 / 1000000000) (Real.log (2751 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37988017 / 100000000) ≤ -Real.log (2560 / 3743) ∧
    -Real.log (2560 / 3743) ≤ (379880171 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 6303)) (n := 12)
    (lo := (37988017 / 100000000)) (hi := (379880171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3743 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3743 / 2560) = 1/(2560 / 3743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37988017 / 100000000) (379880171 / 1000000000) (Real.log (3743 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3743 / 2560) = -Real.log (2560 / 3743) := by
    rw [show ((3743 / 2560) : ℝ) = ((2560 / 3743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (310050019 / 500000000) ≤ -Real.log (1377 / 2560) ∧
    -Real.log (1377 / 2560) ≤ (620100039 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 3937)) (n := 12)
    (lo := (310050019 / 500000000)) (hi := (620100039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1377) = 1/(1377 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-620100039 / 1000000000) (-310050019 / 500000000) (Real.log (1377 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142574057 / 500000000) ≤ -Real.log (1000000 / 1329959) ∧
    -Real.log (1000000 / 1329959) ≤ (57029623 / 200000000) := by
  have h := checkLog_sound (w := (329959 / 2329959)) (n := 12)
    (lo := (142574057 / 500000000)) (hi := (57029623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329959 / 1000000) = 1/(1000000 / 1329959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142574057 / 500000000) (57029623 / 200000000) (Real.log (1329959 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1329959 / 1000000) = -Real.log (1000000 / 1329959) := by
    rw [show ((1329959 / 1000000) : ℝ) = ((1000000 / 1329959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (200208187 / 500000000) ≤ -Real.log (670041 / 1000000) ∧
    -Real.log (670041 / 1000000) ≤ (3203331 / 8000000) := by
  have h := checkLog_sound (w := (329959 / 1670041)) (n := 12)
    (lo := (200208187 / 500000000)) (hi := (3203331 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670041) = 1/(670041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3203331 / 8000000) (-200208187 / 500000000) (Real.log (670041 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (285469877 / 1000000000) ≤ -Real.log (1000000 / 1330387) ∧
    -Real.log (1000000 / 1330387) ≤ (142734939 / 500000000) := by
  have h := checkLog_sound (w := (330387 / 2330387)) (n := 12)
    (lo := (285469877 / 1000000000)) (hi := (142734939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1330387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1330387 / 1000000) = 1/(1000000 / 1330387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (285469877 / 1000000000) (142734939 / 500000000) (Real.log (1330387 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1330387 / 1000000) = -Real.log (1000000 / 1330387) := by
    rw [show ((1330387 / 1000000) : ℝ) = ((1000000 / 1330387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80211069 / 200000000) ≤ -Real.log (669613 / 1000000) ∧
    -Real.log (669613 / 1000000) ≤ (200527673 / 500000000) := by
  have h := checkLog_sound (w := (330387 / 1669613)) (n := 12)
    (lo := (80211069 / 200000000)) (hi := (200527673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 669613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 669613) = 1/(669613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-200527673 / 500000000) (-80211069 / 200000000) (Real.log (669613 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (215566921 / 1000000000) ≤ -Real.log (200000 / 248113) ∧
    -Real.log (200000 / 248113) ≤ (107783461 / 500000000) := by
  have h := checkLog_sound (w := (48113 / 448113)) (n := 12)
    (lo := (215566921 / 1000000000)) (hi := (107783461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248113 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248113 / 200000) = 1/(200000 / 248113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (215566921 / 1000000000) (107783461 / 500000000) (Real.log (248113 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (248113 / 200000) = -Real.log (200000 / 248113) := by
    rw [show ((248113 / 200000) : ℝ) = ((200000 / 248113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (275180543 / 1000000000) ≤ -Real.log (151887 / 200000) ∧
    -Real.log (151887 / 200000) ≤ (537462 / 1953125) := by
  have h := checkLog_sound (w := (48113 / 351887)) (n := 12)
    (lo := (275180543 / 1000000000)) (hi := (537462 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151887) = 1/(151887 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-537462 / 1953125) (-275180543 / 1000000000) (Real.log (151887 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (43166901 / 200000000) ≤ -Real.log (1000000 / 1240897) ∧
    -Real.log (1000000 / 1240897) ≤ (107917253 / 500000000) := by
  have h := checkLog_sound (w := (240897 / 2240897)) (n := 12)
    (lo := (43166901 / 200000000)) (hi := (107917253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240897 / 1000000) = 1/(1000000 / 1240897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (43166901 / 200000000) (107917253 / 500000000) (Real.log (1240897 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1240897 / 1000000) = -Real.log (1000000 / 1240897) := by
    rw [show ((1240897 / 1000000) : ℝ) = ((1000000 / 1240897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55123561 / 200000000) ≤ -Real.log (759103 / 1000000) ∧
    -Real.log (759103 / 1000000) ≤ (137808903 / 500000000) := by
  have h := checkLog_sound (w := (240897 / 1759103)) (n := 12)
    (lo := (55123561 / 200000000)) (hi := (137808903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759103) = 1/(759103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-137808903 / 500000000) (-55123561 / 200000000) (Real.log (759103 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (685564489 / 1000000000) ≤ -Real.log (62500000000 / 124055748081) ∧
    -Real.log (62500000000 / 124055748081) ≤ (68556449 / 100000000) := by
  have h := checkLog_sound (w := (61555748081 / 186555748081)) (n := 12)
    (lo := (685564489 / 1000000000)) (hi := (68556449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124055748081 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124055748081 / 62500000000) = 1/(62500000000 / 124055748081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (685564489 / 1000000000) (68556449 / 100000000) (Real.log (124055748081 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (124055748081 / 62500000000) = -Real.log (62500000000 / 124055748081) := by
    rw [show ((124055748081 / 62500000000) : ℝ) = ((62500000000 / 124055748081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (343262611 / 500000000) ≤ -Real.log (250000000000 / 496699959529) ∧
    -Real.log (250000000000 / 496699959529) ≤ (686525223 / 1000000000) := by
  have h := checkLog_sound (w := (246699959529 / 746699959529)) (n := 12)
    (lo := (343262611 / 500000000)) (hi := (686525223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((496699959529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(496699959529 / 250000000000) = 1/(250000000000 / 496699959529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (343262611 / 500000000) (686525223 / 1000000000) (Real.log (496699959529 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (496699959529 / 250000000000) = -Real.log (250000000000 / 496699959529) := by
    rw [show ((496699959529 / 250000000000) : ℝ) = ((250000000000 / 496699959529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (61343433 / 125000000) ≤ -Real.log (31250000000 / 51048024189) ∧
    -Real.log (31250000000 / 51048024189) ≤ (98149493 / 200000000) := by
  have h := checkLog_sound (w := (19798024189 / 82298024189)) (n := 12)
    (lo := (61343433 / 125000000)) (hi := (98149493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51048024189 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51048024189 / 31250000000) = 1/(31250000000 / 51048024189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (61343433 / 125000000) (98149493 / 200000000) (Real.log (51048024189 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (51048024189 / 31250000000) = -Real.log (31250000000 / 51048024189) := by
    rw [show ((51048024189 / 31250000000) : ℝ) = ((31250000000 / 51048024189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (491452311 / 1000000000) ≤ -Real.log (125000000000 / 204336071653) ∧
    -Real.log (125000000000 / 204336071653) ≤ (61431539 / 125000000) := by
  have h := checkLog_sound (w := (79336071653 / 329336071653)) (n := 12)
    (lo := (491452311 / 1000000000)) (hi := (61431539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204336071653 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204336071653 / 125000000000) = 1/(125000000000 / 204336071653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (491452311 / 1000000000) (61431539 / 125000000) (Real.log (204336071653 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (204336071653 / 125000000000) = -Real.log (125000000000 / 204336071653) := by
    rw [show ((204336071653 / 125000000000) : ℝ) = ((125000000000 / 204336071653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0367

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0368Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0368
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

theorem reflection_log_1_neg : (207871271 / 1000000000) ≤ -Real.log (5120 / 6303) ∧
    -Real.log (5120 / 6303) ≤ (25983909 / 125000000) := by
  have h := checkLog_sound (w := (1183 / 11423)) (n := 12)
    (lo := (207871271 / 1000000000)) (hi := (25983909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6303 / 5120) = 1/(5120 / 6303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (207871271 / 1000000000) (25983909 / 125000000) (Real.log (6303 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6303 / 5120) = -Real.log (5120 / 6303) := by
    rw [show ((6303 / 5120) : ℝ) = ((5120 / 6303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (262735427 / 1000000000) ≤ -Real.log (3937 / 5120) ∧
    -Real.log (3937 / 5120) ≤ (65683857 / 250000000) := by
  have h := checkLog_sound (w := (1183 / 9057)) (n := 12)
    (lo := (262735427 / 1000000000)) (hi := (65683857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3937) = 1/(3937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65683857 / 250000000) (-262735427 / 1000000000) (Real.log (3937 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (207633261 / 1000000000) ≤ -Real.log (10240 / 12603) ∧
    -Real.log (10240 / 12603) ≤ (103816631 / 500000000) := by
  have h := checkLog_sound (w := (2363 / 22843)) (n := 12)
    (lo := (207633261 / 1000000000)) (hi := (103816631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12603 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12603 / 10240) = 1/(10240 / 12603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (207633261 / 1000000000) (103816631 / 500000000) (Real.log (12603 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12603 / 10240) = -Real.log (10240 / 12603) := by
    rw [show ((12603 / 10240) : ℝ) = ((10240 / 12603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (131177249 / 500000000) ≤ -Real.log (7877 / 10240) ∧
    -Real.log (7877 / 10240) ≤ (262354499 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 18117)) (n := 12)
    (lo := (131177249 / 500000000)) (hi := (262354499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7877) = 1/(7877 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-262354499 / 1000000000) (-131177249 / 500000000) (Real.log (7877 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (37988017 / 100000000) ≤ -Real.log (2560 / 3743) ∧
    -Real.log (2560 / 3743) ≤ (379880171 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 6303)) (n := 12)
    (lo := (37988017 / 100000000)) (hi := (379880171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3743 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3743 / 2560) = 1/(2560 / 3743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (37988017 / 100000000) (379880171 / 1000000000) (Real.log (3743 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3743 / 2560) = -Real.log (2560 / 3743) := by
    rw [show ((3743 / 2560) : ℝ) = ((2560 / 3743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (310050019 / 500000000) ≤ -Real.log (1377 / 2560) ∧
    -Real.log (1377 / 2560) ≤ (620100039 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 3937)) (n := 12)
    (lo := (310050019 / 500000000)) (hi := (620100039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1377) = 1/(1377 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-620100039 / 1000000000) (-310050019 / 500000000) (Real.log (1377 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (189739671 / 500000000) ≤ -Real.log (5120 / 7483) ∧
    -Real.log (5120 / 7483) ≤ (379479343 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 12603)) (n := 12)
    (lo := (189739671 / 500000000)) (hi := (379479343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7483 / 5120) = 1/(5120 / 7483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (189739671 / 500000000) (379479343 / 1000000000) (Real.log (7483 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7483 / 5120) = -Real.log (5120 / 7483) := by
    rw [show ((7483 / 5120) : ℝ) = ((5120 / 7483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (619011307 / 1000000000) ≤ -Real.log (2757 / 5120) ∧
    -Real.log (2757 / 5120) ≤ (154752827 / 250000000) := by
  have h := checkLog_sound (w := (2363 / 7877)) (n := 12)
    (lo := (619011307 / 1000000000)) (hi := (154752827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2757) = 1/(2757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154752827 / 250000000) (-619011307 / 1000000000) (Real.log (2757 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (284827 / 1000000) ≤ -Real.log (250000 / 332383) ∧
    -Real.log (250000 / 332383) ≤ (284827001 / 1000000000) := by
  have h := checkLog_sound (w := (82383 / 582383)) (n := 12)
    (lo := (284827 / 1000000)) (hi := (284827001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332383 / 250000) = 1/(250000 / 332383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (284827 / 1000000) (284827001 / 1000000000) (Real.log (332383 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (332383 / 250000) = -Real.log (250000 / 332383) := by
    rw [show ((332383 / 250000) : ℝ) = ((250000 / 332383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199889651 / 500000000) ≤ -Real.log (167617 / 250000) ∧
    -Real.log (167617 / 250000) ≤ (399779303 / 1000000000) := by
  have h := checkLog_sound (w := (82383 / 417617)) (n := 12)
    (lo := (199889651 / 500000000)) (hi := (399779303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 167617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 167617) = 1/(167617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-399779303 / 1000000000) (-199889651 / 500000000) (Real.log (167617 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142574433 / 500000000) ≤ -Real.log (25000 / 33249) ∧
    -Real.log (25000 / 33249) ≤ (285148867 / 1000000000) := by
  have h := checkLog_sound (w := (8249 / 58249)) (n := 12)
    (lo := (142574433 / 500000000)) (hi := (285148867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33249 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33249 / 25000) = 1/(25000 / 33249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142574433 / 500000000) (285148867 / 1000000000) (Real.log (33249 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (33249 / 25000) = -Real.log (25000 / 33249) := by
    rw [show ((33249 / 25000) : ℝ) = ((25000 / 33249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (200208933 / 500000000) ≤ -Real.log (16751 / 25000) ∧
    -Real.log (16751 / 25000) ≤ (400417867 / 1000000000) := by
  have h := checkLog_sound (w := (8249 / 41751)) (n := 12)
    (lo := (200208933 / 500000000)) (hi := (400417867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 16751) = 1/(16751 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-400417867 / 1000000000) (-200208933 / 500000000) (Real.log (16751 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (215300071 / 1000000000) ≤ -Real.log (500000 / 620117) ∧
    -Real.log (500000 / 620117) ≤ (26912509 / 125000000) := by
  have h := checkLog_sound (w := (120117 / 1120117)) (n := 12)
    (lo := (215300071 / 1000000000)) (hi := (26912509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620117 / 500000) = 1/(500000 / 620117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (215300071 / 1000000000) (26912509 / 125000000) (Real.log (620117 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (620117 / 500000) = -Real.log (500000 / 620117) := by
    rw [show ((620117 / 500000) : ℝ) = ((500000 / 620117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (274744787 / 1000000000) ≤ -Real.log (379883 / 500000) ∧
    -Real.log (379883 / 500000) ≤ (68686197 / 250000000) := by
  have h := checkLog_sound (w := (120117 / 879883)) (n := 12)
    (lo := (274744787 / 1000000000)) (hi := (68686197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379883) = 1/(379883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-68686197 / 250000000) (-274744787 / 1000000000) (Real.log (379883 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (215567727 / 1000000000) ≤ -Real.log (500000 / 620283) ∧
    -Real.log (500000 / 620283) ≤ (13472983 / 62500000) := by
  have h := checkLog_sound (w := (120283 / 1120283)) (n := 12)
    (lo := (215567727 / 1000000000)) (hi := (13472983 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620283 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620283 / 500000) = 1/(500000 / 620283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215567727 / 1000000000) (13472983 / 62500000) (Real.log (620283 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (620283 / 500000) = -Real.log (500000 / 620283) := by
    rw [show ((620283 / 500000) : ℝ) = ((500000 / 620283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (275181859 / 1000000000) ≤ -Real.log (379717 / 500000) ∧
    -Real.log (379717 / 500000) ≤ (13759093 / 50000000) := by
  have h := checkLog_sound (w := (120283 / 879717)) (n := 12)
    (lo := (275181859 / 1000000000)) (hi := (13759093 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379717) = 1/(379717 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-13759093 / 50000000) (-275181859 / 1000000000) (Real.log (379717 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (684606303 / 1000000000) ≤ -Real.log (5000000000 / 9914954927) ∧
    -Real.log (5000000000 / 9914954927) ≤ (21393947 / 31250000) := by
  have h := checkLog_sound (w := (4914954927 / 14914954927)) (n := 12)
    (lo := (684606303 / 1000000000)) (hi := (21393947 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9914954927 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9914954927 / 5000000000) = 1/(5000000000 / 9914954927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (684606303 / 1000000000) (21393947 / 31250000) (Real.log (9914954927 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9914954927 / 5000000000) = -Real.log (5000000000 / 9914954927) := by
    rw [show ((9914954927 / 5000000000) : ℝ) = ((5000000000 / 9914954927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (685566733 / 1000000000) ≤ -Real.log (31250000000 / 62028013253) ∧
    -Real.log (31250000000 / 62028013253) ≤ (342783367 / 500000000) := by
  have h := checkLog_sound (w := (30778013253 / 93278013253)) (n := 12)
    (lo := (685566733 / 1000000000)) (hi := (342783367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62028013253 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62028013253 / 31250000000) = 1/(31250000000 / 62028013253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (685566733 / 1000000000) (342783367 / 500000000) (Real.log (62028013253 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (62028013253 / 31250000000) = -Real.log (31250000000 / 62028013253) := by
    rw [show ((62028013253 / 31250000000) : ℝ) = ((31250000000 / 62028013253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (490044859 / 1000000000) ≤ -Real.log (62500000000 / 102024340389) ∧
    -Real.log (62500000000 / 102024340389) ≤ (24502243 / 50000000) := by
  have h := checkLog_sound (w := (39524340389 / 164524340389)) (n := 12)
    (lo := (490044859 / 1000000000)) (hi := (24502243 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102024340389 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102024340389 / 62500000000) = 1/(62500000000 / 102024340389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (490044859 / 1000000000) (24502243 / 50000000) (Real.log (102024340389 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (102024340389 / 62500000000) = -Real.log (62500000000 / 102024340389) := by
    rw [show ((102024340389 / 62500000000) : ℝ) = ((62500000000 / 102024340389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (490749587 / 1000000000) ≤ -Real.log (250000000000 / 408385060453) ∧
    -Real.log (250000000000 / 408385060453) ≤ (122687397 / 250000000) := by
  have h := checkLog_sound (w := (158385060453 / 658385060453)) (n := 12)
    (lo := (490749587 / 1000000000)) (hi := (122687397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408385060453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408385060453 / 250000000000) = 1/(250000000000 / 408385060453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (490749587 / 1000000000) (122687397 / 250000000) (Real.log (408385060453 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (408385060453 / 250000000000) = -Real.log (250000000000 / 408385060453) := by
    rw [show ((408385060453 / 250000000000) : ℝ) = ((250000000000 / 408385060453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0368

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0369Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0369
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

theorem reflection_log_1_neg : (207633261 / 1000000000) ≤ -Real.log (10240 / 12603) ∧
    -Real.log (10240 / 12603) ≤ (103816631 / 500000000) := by
  have h := checkLog_sound (w := (2363 / 22843)) (n := 12)
    (lo := (207633261 / 1000000000)) (hi := (103816631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12603 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12603 / 10240) = 1/(10240 / 12603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (207633261 / 1000000000) (103816631 / 500000000) (Real.log (12603 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12603 / 10240) = -Real.log (10240 / 12603) := by
    rw [show ((12603 / 10240) : ℝ) = ((10240 / 12603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (131177249 / 500000000) ≤ -Real.log (7877 / 10240) ∧
    -Real.log (7877 / 10240) ≤ (262354499 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 18117)) (n := 12)
    (lo := (131177249 / 500000000)) (hi := (262354499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7877) = 1/(7877 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-262354499 / 1000000000) (-131177249 / 500000000) (Real.log (7877 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (103697597 / 500000000) ≤ -Real.log (256 / 315) ∧
    -Real.log (256 / 315) ≤ (41479039 / 200000000) := by
  have h := checkLog_sound (w := (59 / 571)) (n := 12)
    (lo := (103697597 / 500000000)) (hi := (41479039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315 / 256) = 1/(256 / 315) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (103697597 / 500000000) (41479039 / 200000000) (Real.log (315 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (315 / 256) = -Real.log (256 / 315) := by
    rw [show ((315 / 256) : ℝ) = ((256 / 315) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (52394743 / 200000000) ≤ -Real.log (197 / 256) ∧
    -Real.log (197 / 256) ≤ (65493429 / 250000000) := by
  have h := checkLog_sound (w := (59 / 453)) (n := 12)
    (lo := (52394743 / 200000000)) (hi := (65493429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 197) = 1/(197 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65493429 / 250000000) (-52394743 / 200000000) (Real.log (197 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (189739671 / 500000000) ≤ -Real.log (5120 / 7483) ∧
    -Real.log (5120 / 7483) ≤ (379479343 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 12603)) (n := 12)
    (lo := (189739671 / 500000000)) (hi := (379479343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7483 / 5120) = 1/(5120 / 7483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (189739671 / 500000000) (379479343 / 1000000000) (Real.log (7483 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7483 / 5120) = -Real.log (5120 / 7483) := by
    rw [show ((7483 / 5120) : ℝ) = ((5120 / 7483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (619011307 / 1000000000) ≤ -Real.log (2757 / 5120) ∧
    -Real.log (2757 / 5120) ≤ (154752827 / 250000000) := by
  have h := checkLog_sound (w := (2363 / 7877)) (n := 12)
    (lo := (619011307 / 1000000000)) (hi := (154752827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2757) = 1/(2757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-154752827 / 250000000) (-619011307 / 1000000000) (Real.log (2757 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23692397 / 62500000) ≤ -Real.log (128 / 187) ∧
    -Real.log (128 / 187) ≤ (379078353 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 315)) (n := 12)
    (lo := (23692397 / 62500000)) (hi := (379078353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187 / 128) = 1/(128 / 187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23692397 / 62500000) (379078353 / 1000000000) (Real.log (187 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (187 / 128) = -Real.log (128 / 187) := by
    rw [show ((187 / 128) : ℝ) = ((128 / 187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (617923759 / 1000000000) ≤ -Real.log (69 / 128) ∧
    -Real.log (69 / 128) ≤ (7724047 / 12500000) := by
  have h := checkLog_sound (w := (59 / 197)) (n := 12)
    (lo := (617923759 / 1000000000)) (hi := (7724047 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 69) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 69) = 1/(69 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-7724047 / 12500000) (-617923759 / 1000000000) (Real.log (69 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28450503 / 100000000) ≤ -Real.log (62500 / 83069) ∧
    -Real.log (62500 / 83069) ≤ (284505031 / 1000000000) := by
  have h := checkLog_sound (w := (20569 / 145569)) (n := 12)
    (lo := (28450503 / 100000000)) (hi := (284505031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83069 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83069 / 62500) = 1/(62500 / 83069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28450503 / 100000000) (284505031 / 1000000000) (Real.log (83069 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (83069 / 62500) = -Real.log (62500 / 83069) := by
    rw [show ((83069 / 62500) : ℝ) = ((62500 / 83069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199570573 / 500000000) ≤ -Real.log (41931 / 62500) ∧
    -Real.log (41931 / 62500) ≤ (399141147 / 1000000000) := by
  have h := checkLog_sound (w := (20569 / 104431)) (n := 12)
    (lo := (199570573 / 500000000)) (hi := (399141147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 41931) = 1/(41931 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-399141147 / 1000000000) (-199570573 / 500000000) (Real.log (41931 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35603469 / 125000000) ≤ -Real.log (1000000 / 1329533) ∧
    -Real.log (1000000 / 1329533) ≤ (284827753 / 1000000000) := by
  have h := checkLog_sound (w := (329533 / 2329533)) (n := 12)
    (lo := (35603469 / 125000000)) (hi := (284827753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329533 / 1000000) = 1/(1000000 / 1329533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35603469 / 125000000) (284827753 / 1000000000) (Real.log (1329533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1329533 / 1000000) = -Real.log (1000000 / 1329533) := by
    rw [show ((1329533 / 1000000) : ℝ) = ((1000000 / 1329533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (199890397 / 500000000) ≤ -Real.log (670467 / 1000000) ∧
    -Real.log (670467 / 1000000) ≤ (79956159 / 200000000) := by
  have h := checkLog_sound (w := (329533 / 1670467)) (n := 12)
    (lo := (199890397 / 500000000)) (hi := (79956159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670467) = 1/(670467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-79956159 / 200000000) (-199890397 / 500000000) (Real.log (670467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4300663 / 20000000) ≤ -Real.log (1000000 / 1239903) ∧
    -Real.log (1000000 / 1239903) ≤ (215033151 / 1000000000) := by
  have h := checkLog_sound (w := (239903 / 2239903)) (n := 12)
    (lo := (4300663 / 20000000)) (hi := (215033151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239903 / 1000000) = 1/(1000000 / 1239903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4300663 / 20000000) (215033151 / 1000000000) (Real.log (1239903 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1239903 / 1000000) = -Real.log (1000000 / 1239903) := by
    rw [show ((1239903 / 1000000) : ℝ) = ((1000000 / 1239903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (137154611 / 500000000) ≤ -Real.log (760097 / 1000000) ∧
    -Real.log (760097 / 1000000) ≤ (274309223 / 1000000000) := by
  have h := checkLog_sound (w := (239903 / 1760097)) (n := 12)
    (lo := (137154611 / 500000000)) (hi := (274309223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760097) = 1/(760097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-274309223 / 1000000000) (-137154611 / 500000000) (Real.log (760097 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (215300877 / 1000000000) ≤ -Real.log (200000 / 248047) ∧
    -Real.log (200000 / 248047) ≤ (107650439 / 500000000) := by
  have h := checkLog_sound (w := (48047 / 448047)) (n := 12)
    (lo := (215300877 / 1000000000)) (hi := (107650439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248047 / 200000) = 1/(200000 / 248047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215300877 / 1000000000) (107650439 / 500000000) (Real.log (248047 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (248047 / 200000) = -Real.log (200000 / 248047) := by
    rw [show ((248047 / 200000) : ℝ) = ((200000 / 248047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (34343263 / 125000000) ≤ -Real.log (151953 / 200000) ∧
    -Real.log (151953 / 200000) ≤ (54949221 / 200000000) := by
  have h := checkLog_sound (w := (48047 / 351953)) (n := 12)
    (lo := (34343263 / 125000000)) (hi := (54949221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151953) = 1/(151953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-54949221 / 200000000) (-34343263 / 125000000) (Real.log (151953 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (683646177 / 1000000000) ≤ -Real.log (250000000000 / 495271994467) ∧
    -Real.log (250000000000 / 495271994467) ≤ (341823089 / 500000000) := by
  have h := checkLog_sound (w := (245271994467 / 745271994467)) (n := 12)
    (lo := (683646177 / 1000000000)) (hi := (341823089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495271994467 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495271994467 / 250000000000) = 1/(250000000000 / 495271994467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (683646177 / 1000000000) (341823089 / 500000000) (Real.log (495271994467 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (495271994467 / 250000000000) = -Real.log (250000000000 / 495271994467) := by
    rw [show ((495271994467 / 250000000000) : ℝ) = ((250000000000 / 495271994467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (684608547 / 1000000000) ≤ -Real.log (500000000000 / 991497717263) ∧
    -Real.log (500000000000 / 991497717263) ≤ (171152137 / 250000000) := by
  have h := checkLog_sound (w := (491497717263 / 1491497717263)) (n := 12)
    (lo := (684608547 / 1000000000)) (hi := (171152137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991497717263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991497717263 / 500000000000) = 1/(500000000000 / 991497717263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (684608547 / 1000000000) (171152137 / 250000000) (Real.log (991497717263 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (991497717263 / 500000000000) = -Real.log (500000000000 / 991497717263) := by
    rw [show ((991497717263 / 500000000000) : ℝ) = ((500000000000 / 991497717263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (489342373 / 1000000000) ≤ -Real.log (500000000000 / 815621558827) ∧
    -Real.log (500000000000 / 815621558827) ≤ (244671187 / 500000000) := by
  have h := checkLog_sound (w := (315621558827 / 1315621558827)) (n := 12)
    (lo := (489342373 / 1000000000)) (hi := (244671187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815621558827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815621558827 / 500000000000) = 1/(500000000000 / 815621558827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (489342373 / 1000000000) (244671187 / 500000000) (Real.log (815621558827 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (815621558827 / 500000000000) = -Real.log (500000000000 / 815621558827) := by
    rw [show ((815621558827 / 500000000000) : ℝ) = ((500000000000 / 815621558827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (490046981 / 1000000000) ≤ -Real.log (500000000000 / 816196455483) ∧
    -Real.log (500000000000 / 816196455483) ≤ (245023491 / 500000000) := by
  have h := checkLog_sound (w := (316196455483 / 1316196455483)) (n := 12)
    (lo := (490046981 / 1000000000)) (hi := (245023491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((816196455483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(816196455483 / 500000000000) = 1/(500000000000 / 816196455483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (490046981 / 1000000000) (245023491 / 500000000) (Real.log (816196455483 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (816196455483 / 500000000000) = -Real.log (500000000000 / 816196455483) := by
    rw [show ((816196455483 / 500000000000) : ℝ) = ((500000000000 / 816196455483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0369

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0370Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0370
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

theorem reflection_log_1_neg : (103697597 / 500000000) ≤ -Real.log (256 / 315) ∧
    -Real.log (256 / 315) ≤ (41479039 / 200000000) := by
  have h := checkLog_sound (w := (59 / 571)) (n := 12)
    (lo := (103697597 / 500000000)) (hi := (41479039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315 / 256) = 1/(256 / 315) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (103697597 / 500000000) (41479039 / 200000000) (Real.log (315 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (315 / 256) = -Real.log (256 / 315) := by
    rw [show ((315 / 256) : ℝ) = ((256 / 315) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (52394743 / 200000000) ≤ -Real.log (197 / 256) ∧
    -Real.log (197 / 256) ≤ (65493429 / 250000000) := by
  have h := checkLog_sound (w := (59 / 453)) (n := 12)
    (lo := (52394743 / 200000000)) (hi := (65493429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 197) = 1/(197 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65493429 / 250000000) (-52394743 / 200000000) (Real.log (197 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20715707 / 100000000) ≤ -Real.log (10240 / 12597) ∧
    -Real.log (10240 / 12597) ≤ (207157071 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 22837)) (n := 12)
    (lo := (20715707 / 100000000)) (hi := (207157071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12597 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12597 / 10240) = 1/(10240 / 12597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20715707 / 100000000) (207157071 / 1000000000) (Real.log (12597 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12597 / 10240) = -Real.log (10240 / 12597) := by
    rw [show ((12597 / 10240) : ℝ) = ((10240 / 12597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (261593077 / 1000000000) ≤ -Real.log (7883 / 10240) ∧
    -Real.log (7883 / 10240) ≤ (130796539 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 18123)) (n := 12)
    (lo := (261593077 / 1000000000)) (hi := (130796539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7883) = 1/(7883 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-130796539 / 500000000) (-261593077 / 1000000000) (Real.log (7883 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23692397 / 62500000) ≤ -Real.log (128 / 187) ∧
    -Real.log (128 / 187) ≤ (379078353 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 315)) (n := 12)
    (lo := (23692397 / 62500000)) (hi := (379078353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187 / 128) = 1/(128 / 187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23692397 / 62500000) (379078353 / 1000000000) (Real.log (187 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (187 / 128) = -Real.log (128 / 187) := by
    rw [show ((187 / 128) : ℝ) = ((128 / 187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (617923759 / 1000000000) ≤ -Real.log (69 / 128) ∧
    -Real.log (69 / 128) ≤ (7724047 / 12500000) := by
  have h := checkLog_sound (w := (59 / 197)) (n := 12)
    (lo := (617923759 / 1000000000)) (hi := (7724047 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 69) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 69) = 1/(69 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-7724047 / 12500000) (-617923759 / 1000000000) (Real.log (69 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (189338601 / 500000000) ≤ -Real.log (5120 / 7477) ∧
    -Real.log (5120 / 7477) ≤ (378677203 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 12597)) (n := 12)
    (lo := (189338601 / 500000000)) (hi := (378677203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7477 / 5120) = 1/(5120 / 7477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (189338601 / 500000000) (378677203 / 1000000000) (Real.log (7477 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7477 / 5120) = -Real.log (5120 / 7477) := by
    rw [show ((7477 / 5120) : ℝ) = ((5120 / 7477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (616837393 / 1000000000) ≤ -Real.log (2763 / 5120) ∧
    -Real.log (2763 / 5120) ≤ (308418697 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 7883)) (n := 12)
    (lo := (616837393 / 1000000000)) (hi := (308418697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2763) = 1/(2763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-308418697 / 500000000) (-616837393 / 1000000000) (Real.log (2763 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28418371 / 100000000) ≤ -Real.log (1000000 / 1328677) ∧
    -Real.log (1000000 / 1328677) ≤ (284183711 / 1000000000) := by
  have h := checkLog_sound (w := (328677 / 2328677)) (n := 12)
    (lo := (28418371 / 100000000)) (hi := (284183711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328677 / 1000000) = 1/(1000000 / 1328677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28418371 / 100000000) (284183711 / 1000000000) (Real.log (1328677 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1328677 / 1000000) = -Real.log (1000000 / 1328677) := by
    rw [show ((1328677 / 1000000) : ℝ) = ((1000000 / 1328677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199252443 / 500000000) ≤ -Real.log (671323 / 1000000) ∧
    -Real.log (671323 / 1000000) ≤ (398504887 / 1000000000) := by
  have h := checkLog_sound (w := (328677 / 1671323)) (n := 12)
    (lo := (199252443 / 500000000)) (hi := (398504887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671323) = 1/(671323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-398504887 / 1000000000) (-199252443 / 500000000) (Real.log (671323 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (284505783 / 1000000000) ≤ -Real.log (200000 / 265821) ∧
    -Real.log (200000 / 265821) ≤ (35563223 / 125000000) := by
  have h := checkLog_sound (w := (65821 / 465821)) (n := 12)
    (lo := (284505783 / 1000000000)) (hi := (35563223 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265821 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(265821 / 200000) = 1/(200000 / 265821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (284505783 / 1000000000) (35563223 / 125000000) (Real.log (265821 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (265821 / 200000) = -Real.log (200000 / 265821) := by
    rw [show ((265821 / 200000) : ℝ) = ((200000 / 265821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (399142637 / 1000000000) ≤ -Real.log (134179 / 200000) ∧
    -Real.log (134179 / 200000) ≤ (199571319 / 500000000) := by
  have h := checkLog_sound (w := (65821 / 334179)) (n := 12)
    (lo := (399142637 / 1000000000)) (hi := (199571319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 134179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 134179) = 1/(134179 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-199571319 / 500000000) (-399142637 / 1000000000) (Real.log (134179 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42953393 / 200000000) ≤ -Real.log (1000000 / 1239573) ∧
    -Real.log (1000000 / 1239573) ≤ (107383483 / 500000000) := by
  have h := checkLog_sound (w := (239573 / 2239573)) (n := 12)
    (lo := (42953393 / 200000000)) (hi := (107383483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239573 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239573 / 1000000) = 1/(1000000 / 1239573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42953393 / 200000000) (107383483 / 500000000) (Real.log (1239573 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1239573 / 1000000) = -Real.log (1000000 / 1239573) := by
    rw [show ((1239573 / 1000000) : ℝ) = ((1000000 / 1239573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (273875161 / 1000000000) ≤ -Real.log (760427 / 1000000) ∧
    -Real.log (760427 / 1000000) ≤ (136937581 / 500000000) := by
  have h := checkLog_sound (w := (239573 / 1760427)) (n := 12)
    (lo := (273875161 / 1000000000)) (hi := (136937581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760427) = 1/(760427 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-136937581 / 500000000) (-273875161 / 1000000000) (Real.log (760427 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (215033957 / 1000000000) ≤ -Real.log (31250 / 38747) ∧
    -Real.log (31250 / 38747) ≤ (107516979 / 500000000) := by
  have h := checkLog_sound (w := (7497 / 69997)) (n := 12)
    (lo := (215033957 / 1000000000)) (hi := (107516979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38747 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38747 / 31250) = 1/(31250 / 38747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215033957 / 1000000000) (107516979 / 500000000) (Real.log (38747 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38747 / 31250) = -Real.log (31250 / 38747) := by
    rw [show ((38747 / 31250) : ℝ) = ((31250 / 38747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (274310537 / 1000000000) ≤ -Real.log (23753 / 31250) ∧
    -Real.log (23753 / 31250) ≤ (137155269 / 500000000) := by
  have h := checkLog_sound (w := (7497 / 55003)) (n := 12)
    (lo := (274310537 / 1000000000)) (hi := (137155269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23753) = 1/(23753 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-137155269 / 500000000) (-274310537 / 1000000000) (Real.log (23753 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (682688597 / 1000000000) ≤ -Real.log (100000000000 / 197919183463) ∧
    -Real.log (100000000000 / 197919183463) ≤ (341344299 / 500000000) := by
  have h := checkLog_sound (w := (97919183463 / 297919183463)) (n := 12)
    (lo := (682688597 / 1000000000)) (hi := (341344299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197919183463 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197919183463 / 100000000000) = 1/(100000000000 / 197919183463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (682688597 / 1000000000) (341344299 / 500000000) (Real.log (197919183463 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (197919183463 / 100000000000) = -Real.log (100000000000 / 197919183463) := by
    rw [show ((197919183463 / 100000000000) : ℝ) = ((100000000000 / 197919183463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34182421 / 50000000) ≤ -Real.log (500000000000 / 990546210659) ∧
    -Real.log (500000000000 / 990546210659) ≤ (683648421 / 1000000000) := by
  have h := checkLog_sound (w := (490546210659 / 1490546210659)) (n := 12)
    (lo := (34182421 / 50000000)) (hi := (683648421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990546210659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990546210659 / 500000000000) = 1/(500000000000 / 990546210659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34182421 / 50000000) (683648421 / 1000000000) (Real.log (990546210659 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (990546210659 / 500000000000) = -Real.log (500000000000 / 990546210659) := by
    rw [show ((990546210659 / 500000000000) : ℝ) = ((500000000000 / 990546210659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (244321063 / 500000000) ≤ -Real.log (500000000000 / 815050622873) ∧
    -Real.log (500000000000 / 815050622873) ≤ (488642127 / 1000000000) := by
  have h := checkLog_sound (w := (315050622873 / 1315050622873)) (n := 12)
    (lo := (244321063 / 500000000)) (hi := (488642127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815050622873 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815050622873 / 500000000000) = 1/(500000000000 / 815050622873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (244321063 / 500000000) (488642127 / 1000000000) (Real.log (815050622873 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (815050622873 / 500000000000) = -Real.log (500000000000 / 815050622873) := by
    rw [show ((815050622873 / 500000000000) : ℝ) = ((500000000000 / 815050622873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (97868899 / 200000000) ≤ -Real.log (50000000000 / 81562328969) ∧
    -Real.log (50000000000 / 81562328969) ≤ (30584031 / 62500000) := by
  have h := checkLog_sound (w := (31562328969 / 131562328969)) (n := 12)
    (lo := (97868899 / 200000000)) (hi := (30584031 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81562328969 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81562328969 / 50000000000) = 1/(50000000000 / 81562328969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (97868899 / 200000000) (30584031 / 62500000) (Real.log (81562328969 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (81562328969 / 50000000000) = -Real.log (50000000000 / 81562328969) := by
    rw [show ((81562328969 / 50000000000) : ℝ) = ((50000000000 / 81562328969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0370

end


