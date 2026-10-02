-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell030Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell030Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:26:10.1734+00:00
-- url     : https://prove2.me/theorems/7d0b6d13-8539-4978-a446-b273912ef442
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell030Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell031…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell030Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell031Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell032Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell033Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell034Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell035Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell036Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell030Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell031Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell032Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell033Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell034Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell035Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell036Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell030Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell031Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell032Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell033Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell034Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell035Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell036Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell030Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell031Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell032Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell033Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell034Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell035Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell036Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell030Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell030
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (118785117 / 500000000) ≤ -Real.log (5120 / 6493) ∧
    -Real.log (5120 / 6493) ≤ (47514047 / 200000000) := by
  have h := checkLog_sound (w := (1373 / 11613)) (n := 12)
    (lo := (118785117 / 500000000)) (hi := (47514047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6493 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6493 / 5120) = 1/(5120 / 6493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (118785117 / 500000000) (47514047 / 200000000) (Real.log (6493 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6493 / 5120) = -Real.log (5120 / 6493) := by
    rw [show ((6493 / 5120) : ℝ) = ((5120 / 6493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (312198919 / 1000000000) ≤ -Real.log (3747 / 5120) ∧
    -Real.log (3747 / 5120) ≤ (7804973 / 25000000) := by
  have h := checkLog_sound (w := (1373 / 8867)) (n := 12)
    (lo := (312198919 / 1000000000)) (hi := (7804973 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3747) = 1/(3747 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7804973 / 25000000) (-312198919 / 1000000000) (Real.log (3747 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (237108091 / 1000000000) ≤ -Real.log (512 / 649) ∧
    -Real.log (512 / 649) ≤ (59277023 / 250000000) := by
  have h := checkLog_sound (w := (137 / 1161)) (n := 12)
    (lo := (237108091 / 1000000000)) (hi := (59277023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649 / 512) = 1/(512 / 649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (237108091 / 1000000000) (59277023 / 250000000) (Real.log (649 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (649 / 512) = -Real.log (512 / 649) := by
    rw [show ((649 / 512) : ℝ) = ((512 / 649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (311398599 / 1000000000) ≤ -Real.log (375 / 512) ∧
    -Real.log (375 / 512) ≤ (1556993 / 5000000) := by
  have h := checkLog_sound (w := (137 / 887)) (n := 12)
    (lo := (311398599 / 1000000000)) (hi := (1556993 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 375) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 375) = 1/(375 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1556993 / 5000000) (-311398599 / 1000000000) (Real.log (375 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (173775139 / 1000000000) ≤ -Real.log (250000 / 297447) ∧
    -Real.log (250000 / 297447) ≤ (8688757 / 50000000) := by
  have h := checkLog_sound (w := (47447 / 547447)) (n := 12)
    (lo := (173775139 / 1000000000)) (hi := (8688757 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297447 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297447 / 250000) = 1/(250000 / 297447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (173775139 / 1000000000) (8688757 / 50000000) (Real.log (297447 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (297447 / 250000) = -Real.log (250000 / 297447) := by
    rw [show ((297447 / 250000) : ℝ) = ((250000 / 297447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (210459337 / 1000000000) ≤ -Real.log (202553 / 250000) ∧
    -Real.log (202553 / 250000) ≤ (105229669 / 500000000) := by
  have h := checkLog_sound (w := (47447 / 452553)) (n := 12)
    (lo := (210459337 / 1000000000)) (hi := (105229669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202553) = 1/(202553 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-105229669 / 500000000) (-210459337 / 1000000000) (Real.log (202553 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174127241 / 1000000000) ≤ -Real.log (1000000 / 1190207) ∧
    -Real.log (1000000 / 1190207) ≤ (87063621 / 500000000) := by
  have h := checkLog_sound (w := (190207 / 2190207)) (n := 12)
    (lo := (174127241 / 1000000000)) (hi := (87063621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190207 / 1000000) = 1/(1000000 / 1190207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174127241 / 1000000000) (87063621 / 500000000) (Real.log (1190207 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1190207 / 1000000) = -Real.log (1000000 / 1190207) := by
    rw [show ((1190207 / 1000000) : ℝ) = ((1000000 / 1190207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (210976619 / 1000000000) ≤ -Real.log (809793 / 1000000) ∧
    -Real.log (809793 / 1000000) ≤ (10548831 / 50000000) := by
  have h := checkLog_sound (w := (190207 / 1809793)) (n := 12)
    (lo := (210976619 / 1000000000)) (hi := (10548831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809793) = 1/(809793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-10548831 / 50000000) (-210976619 / 1000000000) (Real.log (809793 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31779939 / 250000000) ≤ -Real.log (1000000 / 1135553) ∧
    -Real.log (1000000 / 1135553) ≤ (127119757 / 1000000000) := by
  have h := checkLog_sound (w := (135553 / 2135553)) (n := 12)
    (lo := (31779939 / 250000000)) (hi := (127119757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135553 / 1000000) = 1/(1000000 / 1135553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31779939 / 250000000) (127119757 / 1000000000) (Real.log (1135553 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1135553 / 1000000) = -Real.log (1000000 / 1135553) := by
    rw [show ((1135553 / 1000000) : ℝ) = ((1000000 / 1135553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72832641 / 500000000) ≤ -Real.log (864447 / 1000000) ∧
    -Real.log (864447 / 1000000) ≤ (145665283 / 1000000000) := by
  have h := checkLog_sound (w := (135553 / 1864447)) (n := 12)
    (lo := (72832641 / 500000000)) (hi := (145665283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864447) = 1/(864447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-145665283 / 1000000000) (-72832641 / 500000000) (Real.log (864447 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15923649 / 125000000) ≤ -Real.log (1000000 / 1135859) ∧
    -Real.log (1000000 / 1135859) ≤ (127389193 / 1000000000) := by
  have h := checkLog_sound (w := (135859 / 2135859)) (n := 12)
    (lo := (15923649 / 125000000)) (hi := (127389193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135859 / 1000000) = 1/(1000000 / 1135859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15923649 / 125000000) (127389193 / 1000000000) (Real.log (1135859 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1135859 / 1000000) = -Real.log (1000000 / 1135859) := by
    rw [show ((1135859 / 1000000) : ℝ) = ((1000000 / 1135859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146019329 / 1000000000) ≤ -Real.log (864141 / 1000000) ∧
    -Real.log (864141 / 1000000) ≤ (14601933 / 100000000) := by
  have h := checkLog_sound (w := (135859 / 1864141)) (n := 12)
    (lo := (146019329 / 1000000000)) (hi := (14601933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864141) = 1/(864141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-14601933 / 100000000) (-146019329 / 1000000000) (Real.log (864141 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (54850669 / 100000000) ≤ -Real.log (500000000000 / 865333333333) ∧
    -Real.log (500000000000 / 865333333333) ≤ (548506691 / 1000000000) := by
  have h := checkLog_sound (w := (365333333333 / 1365333333333)) (n := 12)
    (lo := (54850669 / 100000000)) (hi := (548506691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((865333333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(865333333333 / 500000000000) = 1/(500000000000 / 865333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (54850669 / 100000000) (548506691 / 1000000000) (Real.log (865333333333 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (865333333333 / 500000000000) = -Real.log (500000000000 / 865333333333) := by
    rw [show ((865333333333 / 500000000000) : ℝ) = ((500000000000 / 865333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (549769153 / 1000000000) ≤ -Real.log (500000000000 / 866426474513) ∧
    -Real.log (500000000000 / 866426474513) ≤ (274884577 / 500000000) := by
  have h := checkLog_sound (w := (366426474513 / 1366426474513)) (n := 12)
    (lo := (549769153 / 1000000000)) (hi := (274884577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866426474513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866426474513 / 500000000000) = 1/(500000000000 / 866426474513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (549769153 / 1000000000) (274884577 / 500000000) (Real.log (866426474513 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (866426474513 / 500000000000) = -Real.log (500000000000 / 866426474513) := by
    rw [show ((866426474513 / 500000000000) : ℝ) = ((500000000000 / 866426474513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (384234477 / 1000000000) ≤ -Real.log (500000000000 / 734244864307) ∧
    -Real.log (500000000000 / 734244864307) ≤ (192117239 / 500000000) := by
  have h := checkLog_sound (w := (234244864307 / 1234244864307)) (n := 12)
    (lo := (384234477 / 1000000000)) (hi := (192117239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734244864307 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734244864307 / 500000000000) = 1/(500000000000 / 734244864307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (384234477 / 1000000000) (192117239 / 500000000) (Real.log (734244864307 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (734244864307 / 500000000000) = -Real.log (500000000000 / 734244864307) := by
    rw [show ((734244864307 / 500000000000) : ℝ) = ((500000000000 / 734244864307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (385103861 / 1000000000) ≤ -Real.log (50000000000 / 73488348257) ∧
    -Real.log (50000000000 / 73488348257) ≤ (192551931 / 500000000) := by
  have h := checkLog_sound (w := (23488348257 / 123488348257)) (n := 12)
    (lo := (385103861 / 1000000000)) (hi := (192551931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73488348257 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73488348257 / 50000000000) = 1/(50000000000 / 73488348257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (385103861 / 1000000000) (192551931 / 500000000) (Real.log (73488348257 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (73488348257 / 50000000000) = -Real.log (50000000000 / 73488348257) := by
    rw [show ((73488348257 / 50000000000) : ℝ) = ((50000000000 / 73488348257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (272785039 / 1000000000) ≤ -Real.log (500000000000 / 656808919459) ∧
    -Real.log (500000000000 / 656808919459) ≤ (3409813 / 12500000) := by
  have h := checkLog_sound (w := (156808919459 / 1156808919459)) (n := 12)
    (lo := (272785039 / 1000000000)) (hi := (3409813 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656808919459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656808919459 / 500000000000) = 1/(500000000000 / 656808919459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (272785039 / 1000000000) (3409813 / 12500000) (Real.log (656808919459 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (656808919459 / 500000000000) = -Real.log (500000000000 / 656808919459) := by
    rw [show ((656808919459 / 500000000000) : ℝ) = ((500000000000 / 656808919459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (273408521 / 1000000000) ≤ -Real.log (500000000000 / 657218555769) ∧
    -Real.log (500000000000 / 657218555769) ≤ (136704261 / 500000000) := by
  have h := checkLog_sound (w := (157218555769 / 1157218555769)) (n := 12)
    (lo := (273408521 / 1000000000)) (hi := (136704261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657218555769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657218555769 / 500000000000) = 1/(500000000000 / 657218555769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (273408521 / 1000000000) (136704261 / 500000000) (Real.log (657218555769 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (657218555769 / 500000000000) = -Real.log (500000000000 / 657218555769) := by
    rw [show ((657218555769 / 500000000000) : ℝ) = ((500000000000 / 657218555769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2328767 / 125000000) ≤ -Real.log (981542332119 / 1000000000000) ∧
    -Real.log (981542332119 / 1000000000000) ≤ (18630137 / 1000000000) := by
  have h := checkLog_sound (w := (18457667881 / 1981542332119)) (n := 12)
    (lo := (2328767 / 125000000)) (hi := (18630137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981542332119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981542332119) = 1/(981542332119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18630137 / 1000000000) (-2328767 / 125000000) (Real.log (981542332119 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (741821 / 40000000) ≤ -Real.log (981625384191 / 1000000000000) ∧
    -Real.log (981625384191 / 1000000000000) ≤ (9272763 / 500000000) := by
  have h := checkLog_sound (w := (18374615809 / 1981625384191)) (n := 12)
    (lo := (741821 / 40000000)) (hi := (9272763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981625384191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981625384191) = 1/(981625384191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9272763 / 500000000) (-741821 / 40000000) (Real.log (981625384191 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell030

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell031Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell031
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (238032163 / 1000000000) ≤ -Real.log (160 / 203) ∧
    -Real.log (160 / 203) ≤ (59508041 / 250000000) := by
  have h := checkLog_sound (w := (43 / 363)) (n := 12)
    (lo := (238032163 / 1000000000)) (hi := (59508041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203 / 160) = 1/(160 / 203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (238032163 / 1000000000) (59508041 / 250000000) (Real.log (203 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (203 / 160) = -Real.log (160 / 203) := by
    rw [show ((203 / 160) : ℝ) = ((160 / 203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7824997 / 25000000) ≤ -Real.log (117 / 160) ∧
    -Real.log (117 / 160) ≤ (312999881 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 117) = 1/(117 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-312999881 / 1000000000) (-7824997 / 25000000) (Real.log (117 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (118785117 / 500000000) ≤ -Real.log (5120 / 6493) ∧
    -Real.log (5120 / 6493) ≤ (47514047 / 200000000) := by
  have h := checkLog_sound (w := (1373 / 11613)) (n := 12)
    (lo := (118785117 / 500000000)) (hi := (47514047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6493 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6493 / 5120) = 1/(5120 / 6493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (118785117 / 500000000) (47514047 / 200000000) (Real.log (6493 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6493 / 5120) = -Real.log (5120 / 6493) := by
    rw [show ((6493 / 5120) : ℝ) = ((5120 / 6493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (312198919 / 1000000000) ≤ -Real.log (3747 / 5120) ∧
    -Real.log (3747 / 5120) ≤ (7804973 / 25000000) := by
  have h := checkLog_sound (w := (1373 / 8867)) (n := 12)
    (lo := (312198919 / 1000000000)) (hi := (7804973 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3747) = 1/(3747 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7804973 / 25000000) (-312198919 / 1000000000) (Real.log (3747 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (174126401 / 1000000000) ≤ -Real.log (500000 / 595103) ∧
    -Real.log (500000 / 595103) ≤ (87063201 / 500000000) := by
  have h := checkLog_sound (w := (95103 / 1095103)) (n := 12)
    (lo := (174126401 / 1000000000)) (hi := (87063201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595103 / 500000) = 1/(500000 / 595103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (174126401 / 1000000000) (87063201 / 500000000) (Real.log (595103 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (595103 / 500000) = -Real.log (500000 / 595103) := by
    rw [show ((595103 / 500000) : ℝ) = ((500000 / 595103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (26371923 / 125000000) ≤ -Real.log (404897 / 500000) ∧
    -Real.log (404897 / 500000) ≤ (42195077 / 200000000) := by
  have h := checkLog_sound (w := (95103 / 904897)) (n := 12)
    (lo := (26371923 / 125000000)) (hi := (42195077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404897) = 1/(404897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-42195077 / 200000000) (-26371923 / 125000000) (Real.log (404897 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174478379 / 1000000000) ≤ -Real.log (320 / 381) ∧
    -Real.log (320 / 381) ≤ (8723919 / 50000000) := by
  have h := checkLog_sound (w := (61 / 701)) (n := 12)
    (lo := (174478379 / 1000000000)) (hi := (8723919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 320) = 1/(320 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174478379 / 1000000000) (8723919 / 50000000) (Real.log (381 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (381 / 320) = -Real.log (320 / 381) := by
    rw [show ((381 / 320) : ℝ) = ((320 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (105746467 / 500000000) ≤ -Real.log (259 / 320) ∧
    -Real.log (259 / 320) ≤ (42298587 / 200000000) := by
  have h := checkLog_sound (w := (61 / 579)) (n := 12)
    (lo := (105746467 / 500000000)) (hi := (42298587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 259) = 1/(259 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-42298587 / 200000000) (-105746467 / 500000000) (Real.log (259 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15923539 / 125000000) ≤ -Real.log (500000 / 567929) ∧
    -Real.log (500000 / 567929) ≤ (127388313 / 1000000000) := by
  have h := checkLog_sound (w := (67929 / 1067929)) (n := 12)
    (lo := (15923539 / 125000000)) (hi := (127388313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567929 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567929 / 500000) = 1/(500000 / 567929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15923539 / 125000000) (127388313 / 1000000000) (Real.log (567929 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (567929 / 500000) = -Real.log (500000 / 567929) := by
    rw [show ((567929 / 500000) : ℝ) = ((500000 / 567929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (146018171 / 1000000000) ≤ -Real.log (432071 / 500000) ∧
    -Real.log (432071 / 500000) ≤ (36504543 / 250000000) := by
  have h := checkLog_sound (w := (67929 / 932071)) (n := 12)
    (lo := (146018171 / 1000000000)) (hi := (36504543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432071) = 1/(432071 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36504543 / 250000000) (-146018171 / 1000000000) (Real.log (432071 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31914419 / 250000000) ≤ -Real.log (250000 / 284041) ∧
    -Real.log (250000 / 284041) ≤ (127657677 / 1000000000) := by
  have h := checkLog_sound (w := (34041 / 534041)) (n := 12)
    (lo := (31914419 / 250000000)) (hi := (127657677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284041 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284041 / 250000) = 1/(250000 / 284041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31914419 / 250000000) (127657677 / 1000000000) (Real.log (284041 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (284041 / 250000) = -Real.log (250000 / 284041) := by
    rw [show ((284041 / 250000) : ℝ) = ((250000 / 284041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146372343 / 1000000000) ≤ -Real.log (215959 / 250000) ∧
    -Real.log (215959 / 250000) ≤ (18296543 / 125000000) := by
  have h := checkLog_sound (w := (34041 / 465959)) (n := 12)
    (lo := (146372343 / 1000000000)) (hi := (18296543 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215959) = 1/(215959 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-18296543 / 125000000) (-146372343 / 1000000000) (Real.log (215959 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (549769153 / 1000000000) ≤ -Real.log (31250000000 / 54151654657) ∧
    -Real.log (31250000000 / 54151654657) ≤ (274884577 / 500000000) := by
  have h := checkLog_sound (w := (22901654657 / 85401654657)) (n := 12)
    (lo := (549769153 / 1000000000)) (hi := (274884577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54151654657 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54151654657 / 31250000000) = 1/(31250000000 / 54151654657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (549769153 / 1000000000) (274884577 / 500000000) (Real.log (54151654657 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (54151654657 / 31250000000) = -Real.log (31250000000 / 54151654657) := by
    rw [show ((54151654657 / 31250000000) : ℝ) = ((31250000000 / 54151654657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (137758011 / 250000000) ≤ -Real.log (250000000000 / 433760683761) ∧
    -Real.log (250000000000 / 433760683761) ≤ (110206409 / 200000000) := by
  have h := checkLog_sound (w := (183760683761 / 683760683761)) (n := 12)
    (lo := (137758011 / 250000000)) (hi := (110206409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433760683761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433760683761 / 250000000000) = 1/(250000000000 / 433760683761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (137758011 / 250000000) (110206409 / 200000000) (Real.log (433760683761 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (433760683761 / 250000000000) = -Real.log (250000000000 / 433760683761) := by
    rw [show ((433760683761 / 250000000000) : ℝ) = ((250000000000 / 433760683761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (192550893 / 500000000) ≤ -Real.log (500000000000 / 734881957633) ∧
    -Real.log (500000000000 / 734881957633) ≤ (385101787 / 1000000000) := by
  have h := checkLog_sound (w := (234881957633 / 1234881957633)) (n := 12)
    (lo := (192550893 / 500000000)) (hi := (385101787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734881957633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734881957633 / 500000000000) = 1/(500000000000 / 734881957633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192550893 / 500000000) (385101787 / 1000000000) (Real.log (734881957633 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (734881957633 / 500000000000) = -Real.log (500000000000 / 734881957633) := by
    rw [show ((734881957633 / 500000000000) : ℝ) = ((500000000000 / 734881957633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (385971313 / 1000000000) ≤ -Real.log (250000000000 / 367760617761) ∧
    -Real.log (250000000000 / 367760617761) ≤ (192985657 / 500000000) := by
  have h := checkLog_sound (w := (117760617761 / 617760617761)) (n := 12)
    (lo := (385971313 / 1000000000)) (hi := (192985657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367760617761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367760617761 / 250000000000) = 1/(250000000000 / 367760617761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (385971313 / 1000000000) (192985657 / 500000000) (Real.log (367760617761 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (367760617761 / 250000000000) = -Real.log (250000000000 / 367760617761) := by
    rw [show ((367760617761 / 250000000000) : ℝ) = ((250000000000 / 367760617761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (68351621 / 250000000) ≤ -Real.log (250000000000 / 328608608307) ∧
    -Real.log (250000000000 / 328608608307) ≤ (54681297 / 200000000) := by
  have h := checkLog_sound (w := (78608608307 / 578608608307)) (n := 12)
    (lo := (68351621 / 250000000)) (hi := (54681297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328608608307 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328608608307 / 250000000000) = 1/(250000000000 / 328608608307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (68351621 / 250000000) (54681297 / 200000000) (Real.log (328608608307 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (328608608307 / 250000000000) = -Real.log (250000000000 / 328608608307) := by
    rw [show ((328608608307 / 250000000000) : ℝ) = ((250000000000 / 328608608307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (274030019 / 1000000000) ≤ -Real.log (50000000000 / 65762714219) ∧
    -Real.log (50000000000 / 65762714219) ≤ (13701501 / 50000000) := by
  have h := checkLog_sound (w := (15762714219 / 115762714219)) (n := 12)
    (lo := (274030019 / 1000000000)) (hi := (13701501 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65762714219 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65762714219 / 50000000000) = 1/(50000000000 / 65762714219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (274030019 / 1000000000) (13701501 / 50000000) (Real.log (65762714219 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65762714219 / 50000000000) = -Real.log (50000000000 / 65762714219) := by
    rw [show ((65762714219 / 50000000000) : ℝ) = ((50000000000 / 65762714219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9357333 / 500000000) ≤ -Real.log (61341210319 / 62500000000) ∧
    -Real.log (61341210319 / 62500000000) ≤ (18714667 / 1000000000) := by
  have h := checkLog_sound (w := (1158789681 / 123841210319)) (n := 12)
    (lo := (9357333 / 500000000)) (hi := (18714667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61341210319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61341210319) = 1/(61341210319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18714667 / 1000000000) (-9357333 / 500000000) (Real.log (61341210319 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18629859 / 1000000000) ≤ -Real.log (245385650959 / 250000000000) ∧
    -Real.log (245385650959 / 250000000000) ≤ (931493 / 50000000) := by
  have h := checkLog_sound (w := (4614349041 / 495385650959)) (n := 12)
    (lo := (18629859 / 1000000000)) (hi := (931493 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245385650959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245385650959) = 1/(245385650959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-931493 / 50000000) (-18629859 / 1000000000) (Real.log (245385650959 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell031

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell032Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell032
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (238493879 / 1000000000) ≤ -Real.log (5120 / 6499) ∧
    -Real.log (5120 / 6499) ≤ (5962347 / 25000000) := by
  have h := checkLog_sound (w := (1379 / 11619)) (n := 12)
    (lo := (238493879 / 1000000000)) (hi := (5962347 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6499 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6499 / 5120) = 1/(5120 / 6499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (238493879 / 1000000000) (5962347 / 25000000) (Real.log (6499 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6499 / 5120) = -Real.log (5120 / 6499) := by
    rw [show ((6499 / 5120) : ℝ) = ((5120 / 6499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (313801483 / 1000000000) ≤ -Real.log (3741 / 5120) ∧
    -Real.log (3741 / 5120) ≤ (78450371 / 250000000) := by
  have h := checkLog_sound (w := (1379 / 8861)) (n := 12)
    (lo := (313801483 / 1000000000)) (hi := (78450371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3741) = 1/(3741 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-78450371 / 250000000) (-313801483 / 1000000000) (Real.log (3741 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (238032163 / 1000000000) ≤ -Real.log (160 / 203) ∧
    -Real.log (160 / 203) ≤ (59508041 / 250000000) := by
  have h := checkLog_sound (w := (43 / 363)) (n := 12)
    (lo := (238032163 / 1000000000)) (hi := (59508041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203 / 160) = 1/(160 / 203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (238032163 / 1000000000) (59508041 / 250000000) (Real.log (203 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (203 / 160) = -Real.log (160 / 203) := by
    rw [show ((203 / 160) : ℝ) = ((160 / 203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7824997 / 25000000) ≤ -Real.log (117 / 160) ∧
    -Real.log (117 / 160) ≤ (312999881 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 117) = 1/(117 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-312999881 / 1000000000) (-7824997 / 25000000) (Real.log (117 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (174477539 / 1000000000) ≤ -Real.log (31250 / 37207) ∧
    -Real.log (31250 / 37207) ≤ (8723877 / 50000000) := by
  have h := checkLog_sound (w := (5957 / 68457)) (n := 12)
    (lo := (174477539 / 1000000000)) (hi := (8723877 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37207 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37207 / 31250) = 1/(31250 / 37207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (174477539 / 1000000000) (8723877 / 50000000) (Real.log (37207 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37207 / 31250) = -Real.log (31250 / 37207) := by
    rw [show ((37207 / 31250) : ℝ) = ((31250 / 37207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (105745849 / 500000000) ≤ -Real.log (25293 / 31250) ∧
    -Real.log (25293 / 31250) ≤ (211491699 / 1000000000) := by
  have h := checkLog_sound (w := (5957 / 56543)) (n := 12)
    (lo := (105745849 / 500000000)) (hi := (211491699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25293) = 1/(25293 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-211491699 / 1000000000) (-105745849 / 500000000) (Real.log (25293 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174829393 / 1000000000) ≤ -Real.log (1000000 / 1191043) ∧
    -Real.log (1000000 / 1191043) ≤ (87414697 / 500000000) := by
  have h := checkLog_sound (w := (191043 / 2191043)) (n := 12)
    (lo := (174829393 / 1000000000)) (hi := (87414697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191043 / 1000000) = 1/(1000000 / 1191043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174829393 / 1000000000) (87414697 / 500000000) (Real.log (1191043 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1191043 / 1000000) = -Real.log (1000000 / 1191043) := by
    rw [show ((1191043 / 1000000) : ℝ) = ((1000000 / 1191043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (42401903 / 200000000) ≤ -Real.log (808957 / 1000000) ∧
    -Real.log (808957 / 1000000) ≤ (53002379 / 250000000) := by
  have h := checkLog_sound (w := (191043 / 1808957)) (n := 12)
    (lo := (42401903 / 200000000)) (hi := (53002379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808957) = 1/(808957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-53002379 / 250000000) (-42401903 / 200000000) (Real.log (808957 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (25531359 / 200000000) ≤ -Real.log (1000000 / 1136163) ∧
    -Real.log (1000000 / 1136163) ≤ (31914199 / 250000000) := by
  have h := checkLog_sound (w := (136163 / 2136163)) (n := 12)
    (lo := (25531359 / 200000000)) (hi := (31914199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136163 / 1000000) = 1/(1000000 / 1136163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (25531359 / 200000000) (31914199 / 250000000) (Real.log (1136163 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1136163 / 1000000) = -Real.log (1000000 / 1136163) := by
    rw [show ((1136163 / 1000000) : ℝ) = ((1000000 / 1136163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (29274237 / 200000000) ≤ -Real.log (863837 / 1000000) ∧
    -Real.log (863837 / 1000000) ≤ (73185593 / 500000000) := by
  have h := checkLog_sound (w := (136163 / 1863837)) (n := 12)
    (lo := (29274237 / 200000000)) (hi := (73185593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863837) = 1/(863837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-73185593 / 500000000) (-29274237 / 200000000) (Real.log (863837 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127926087 / 1000000000) ≤ -Real.log (1000000 / 1136469) ∧
    -Real.log (1000000 / 1136469) ≤ (15990761 / 125000000) := by
  have h := checkLog_sound (w := (136469 / 2136469)) (n := 12)
    (lo := (127926087 / 1000000000)) (hi := (15990761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136469 / 1000000) = 1/(1000000 / 1136469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127926087 / 1000000000) (15990761 / 125000000) (Real.log (1136469 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1136469 / 1000000) = -Real.log (1000000 / 1136469) := by
    rw [show ((1136469 / 1000000) : ℝ) = ((1000000 / 1136469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146725481 / 1000000000) ≤ -Real.log (863531 / 1000000) ∧
    -Real.log (863531 / 1000000) ≤ (73362741 / 500000000) := by
  have h := checkLog_sound (w := (136469 / 1863531)) (n := 12)
    (lo := (146725481 / 1000000000)) (hi := (73362741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863531) = 1/(863531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-73362741 / 500000000) (-146725481 / 1000000000) (Real.log (863531 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (137758011 / 250000000) ≤ -Real.log (500000000000 / 867521367521) ∧
    -Real.log (500000000000 / 867521367521) ≤ (110206409 / 200000000) := by
  have h := checkLog_sound (w := (367521367521 / 1367521367521)) (n := 12)
    (lo := (137758011 / 250000000)) (hi := (110206409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867521367521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867521367521 / 500000000000) = 1/(500000000000 / 867521367521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (137758011 / 250000000) (110206409 / 200000000) (Real.log (867521367521 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (867521367521 / 500000000000) = -Real.log (500000000000 / 867521367521) := by
    rw [show ((867521367521 / 500000000000) : ℝ) = ((500000000000 / 867521367521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (552295363 / 1000000000) ≤ -Real.log (250000000000 / 434309008287) ∧
    -Real.log (250000000000 / 434309008287) ≤ (138073841 / 250000000) := by
  have h := checkLog_sound (w := (184309008287 / 684309008287)) (n := 12)
    (lo := (552295363 / 1000000000)) (hi := (138073841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434309008287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434309008287 / 250000000000) = 1/(250000000000 / 434309008287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (552295363 / 1000000000) (138073841 / 250000000) (Real.log (434309008287 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (434309008287 / 250000000000) = -Real.log (250000000000 / 434309008287) := by
    rw [show ((434309008287 / 250000000000) : ℝ) = ((250000000000 / 434309008287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (192984619 / 500000000) ≤ -Real.log (50000000000 / 73551970901) ∧
    -Real.log (50000000000 / 73551970901) ≤ (385969239 / 1000000000) := by
  have h := checkLog_sound (w := (23551970901 / 123551970901)) (n := 12)
    (lo := (192984619 / 500000000)) (hi := (385969239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73551970901 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73551970901 / 50000000000) = 1/(50000000000 / 73551970901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192984619 / 500000000) (385969239 / 1000000000) (Real.log (73551970901 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (73551970901 / 50000000000) = -Real.log (50000000000 / 73551970901) := by
    rw [show ((73551970901 / 50000000000) : ℝ) = ((50000000000 / 73551970901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (386838909 / 1000000000) ≤ -Real.log (500000000000 / 736159647547) ∧
    -Real.log (500000000000 / 736159647547) ≤ (38683891 / 100000000) := by
  have h := checkLog_sound (w := (236159647547 / 1236159647547)) (n := 12)
    (lo := (386838909 / 1000000000)) (hi := (38683891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736159647547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736159647547 / 500000000000) = 1/(500000000000 / 736159647547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (386838909 / 1000000000) (38683891 / 100000000) (Real.log (736159647547 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (736159647547 / 500000000000) = -Real.log (500000000000 / 736159647547) := by
    rw [show ((736159647547 / 500000000000) : ℝ) = ((500000000000 / 736159647547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (274027981 / 1000000000) ≤ -Real.log (500000000000 / 657625802089) ∧
    -Real.log (500000000000 / 657625802089) ≤ (137013991 / 500000000) := by
  have h := checkLog_sound (w := (157625802089 / 1157625802089)) (n := 12)
    (lo := (274027981 / 1000000000)) (hi := (137013991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657625802089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657625802089 / 500000000000) = 1/(500000000000 / 657625802089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (274027981 / 1000000000) (137013991 / 500000000) (Real.log (657625802089 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (657625802089 / 500000000000) = -Real.log (500000000000 / 657625802089) := by
    rw [show ((657625802089 / 500000000000) : ℝ) = ((500000000000 / 657625802089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (17165723 / 62500000) ≤ -Real.log (500000000000 / 658036017237) ∧
    -Real.log (500000000000 / 658036017237) ≤ (274651569 / 1000000000) := by
  have h := checkLog_sound (w := (158036017237 / 1158036017237)) (n := 12)
    (lo := (17165723 / 62500000)) (hi := (274651569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658036017237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658036017237 / 500000000000) = 1/(500000000000 / 658036017237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (17165723 / 62500000) (274651569 / 1000000000) (Real.log (658036017237 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (658036017237 / 500000000000) = -Real.log (500000000000 / 658036017237) := by
    rw [show ((658036017237 / 500000000000) : ℝ) = ((500000000000 / 658036017237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9399697 / 500000000) ≤ -Real.log (981376212039 / 1000000000000) ∧
    -Real.log (981376212039 / 1000000000000) ≤ (3759879 / 200000000) := by
  have h := checkLog_sound (w := (18623787961 / 1981376212039)) (n := 12)
    (lo := (9399697 / 500000000)) (hi := (3759879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981376212039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981376212039) = 1/(981376212039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3759879 / 200000000) (-9399697 / 500000000) (Real.log (981376212039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18714389 / 1000000000) ≤ -Real.log (981459637431 / 1000000000000) ∧
    -Real.log (981459637431 / 1000000000000) ≤ (1871439 / 100000000) := by
  have h := checkLog_sound (w := (18540362569 / 1981459637431)) (n := 12)
    (lo := (18714389 / 1000000000)) (hi := (1871439 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981459637431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981459637431) = 1/(981459637431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1871439 / 100000000) (-18714389 / 1000000000) (Real.log (981459637431 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell032

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell033Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell033
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (119477691 / 500000000) ≤ -Real.log (2560 / 3251) ∧
    -Real.log (2560 / 3251) ≤ (238955383 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 5811)) (n := 12)
    (lo := (119477691 / 500000000)) (hi := (238955383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3251 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3251 / 2560) = 1/(2560 / 3251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (119477691 / 500000000) (238955383 / 1000000000) (Real.log (3251 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3251 / 2560) = -Real.log (2560 / 3251) := by
    rw [show ((3251 / 2560) : ℝ) = ((2560 / 3251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31460373 / 100000000) ≤ -Real.log (1869 / 2560) ∧
    -Real.log (1869 / 2560) ≤ (314603731 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 4429)) (n := 12)
    (lo := (31460373 / 100000000)) (hi := (314603731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1869) = 1/(1869 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-314603731 / 1000000000) (-31460373 / 100000000) (Real.log (1869 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (238493879 / 1000000000) ≤ -Real.log (5120 / 6499) ∧
    -Real.log (5120 / 6499) ≤ (5962347 / 25000000) := by
  have h := checkLog_sound (w := (1379 / 11619)) (n := 12)
    (lo := (238493879 / 1000000000)) (hi := (5962347 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6499 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6499 / 5120) = 1/(5120 / 6499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (238493879 / 1000000000) (5962347 / 25000000) (Real.log (6499 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6499 / 5120) = -Real.log (5120 / 6499) := by
    rw [show ((6499 / 5120) : ℝ) = ((5120 / 6499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (313801483 / 1000000000) ≤ -Real.log (3741 / 5120) ∧
    -Real.log (3741 / 5120) ≤ (78450371 / 250000000) := by
  have h := checkLog_sound (w := (1379 / 8861)) (n := 12)
    (lo := (313801483 / 1000000000)) (hi := (78450371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3741) = 1/(3741 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78450371 / 250000000) (-313801483 / 1000000000) (Real.log (3741 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87414277 / 500000000) ≤ -Real.log (500000 / 595521) ∧
    -Real.log (500000 / 595521) ≤ (34965711 / 200000000) := by
  have h := checkLog_sound (w := (95521 / 1095521)) (n := 12)
    (lo := (87414277 / 500000000)) (hi := (34965711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595521 / 500000) = 1/(500000 / 595521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87414277 / 500000000) (34965711 / 200000000) (Real.log (595521 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (595521 / 500000) = -Real.log (500000 / 595521) := by
    rw [show ((595521 / 500000) : ℝ) = ((500000 / 595521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (212008279 / 1000000000) ≤ -Real.log (404479 / 500000) ∧
    -Real.log (404479 / 500000) ≤ (5300207 / 25000000) := by
  have h := checkLog_sound (w := (95521 / 904479)) (n := 12)
    (lo := (212008279 / 1000000000)) (hi := (5300207 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404479) = 1/(404479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5300207 / 25000000) (-212008279 / 1000000000) (Real.log (404479 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43795281 / 250000000) ≤ -Real.log (500000 / 595731) ∧
    -Real.log (500000 / 595731) ≤ (1401449 / 8000000) := by
  have h := checkLog_sound (w := (95731 / 1095731)) (n := 12)
    (lo := (43795281 / 250000000)) (hi := (1401449 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595731 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595731 / 500000) = 1/(500000 / 595731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43795281 / 250000000) (1401449 / 8000000) (Real.log (595731 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (595731 / 500000) = -Real.log (500000 / 595731) := by
    rw [show ((595731 / 500000) : ℝ) = ((500000 / 595731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (531319 / 2500000) ≤ -Real.log (404269 / 500000) ∧
    -Real.log (404269 / 500000) ≤ (212527601 / 1000000000) := by
  have h := checkLog_sound (w := (95731 / 904269)) (n := 12)
    (lo := (531319 / 2500000)) (hi := (212527601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404269) = 1/(404269 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-212527601 / 1000000000) (-531319 / 2500000) (Real.log (404269 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (127925207 / 1000000000) ≤ -Real.log (250000 / 284117) ∧
    -Real.log (250000 / 284117) ≤ (15990651 / 125000000) := by
  have h := checkLog_sound (w := (34117 / 534117)) (n := 12)
    (lo := (127925207 / 1000000000)) (hi := (15990651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284117 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284117 / 250000) = 1/(250000 / 284117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (127925207 / 1000000000) (15990651 / 125000000) (Real.log (284117 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (284117 / 250000) = -Real.log (250000 / 284117) := by
    rw [show ((284117 / 250000) : ℝ) = ((250000 / 284117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (146724323 / 1000000000) ≤ -Real.log (215883 / 250000) ∧
    -Real.log (215883 / 250000) ≤ (36681081 / 250000000) := by
  have h := checkLog_sound (w := (34117 / 465883)) (n := 12)
    (lo := (146724323 / 1000000000)) (hi := (36681081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215883) = 1/(215883 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36681081 / 250000000) (-146724323 / 1000000000) (Real.log (215883 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64097653 / 500000000) ≤ -Real.log (40000 / 45471) ∧
    -Real.log (40000 / 45471) ≤ (128195307 / 1000000000) := by
  have h := checkLog_sound (w := (5471 / 85471)) (n := 12)
    (lo := (64097653 / 500000000)) (hi := (128195307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45471 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45471 / 40000) = 1/(40000 / 45471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64097653 / 500000000) (128195307 / 1000000000) (Real.log (45471 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (45471 / 40000) = -Real.log (40000 / 45471) := by
    rw [show ((45471 / 40000) : ℝ) = ((40000 / 45471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (147079903 / 1000000000) ≤ -Real.log (34529 / 40000) ∧
    -Real.log (34529 / 40000) ≤ (4596247 / 31250000) := by
  have h := checkLog_sound (w := (5471 / 74529)) (n := 12)
    (lo := (147079903 / 1000000000)) (hi := (4596247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34529) = 1/(34529 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4596247 / 31250000) (-147079903 / 1000000000) (Real.log (34529 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (552295363 / 1000000000) ≤ -Real.log (500000000000 / 868618016573) ∧
    -Real.log (500000000000 / 868618016573) ≤ (138073841 / 250000000) := by
  have h := checkLog_sound (w := (368618016573 / 1368618016573)) (n := 12)
    (lo := (552295363 / 1000000000)) (hi := (138073841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868618016573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868618016573 / 500000000000) = 1/(500000000000 / 868618016573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (552295363 / 1000000000) (138073841 / 250000000) (Real.log (868618016573 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (868618016573 / 500000000000) = -Real.log (500000000000 / 868618016573) := by
    rw [show ((868618016573 / 500000000000) : ℝ) = ((500000000000 / 868618016573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69194889 / 125000000) ≤ -Real.log (500000000000 / 869716425897) ∧
    -Real.log (500000000000 / 869716425897) ≤ (553559113 / 1000000000) := by
  have h := checkLog_sound (w := (369716425897 / 1369716425897)) (n := 12)
    (lo := (69194889 / 125000000)) (hi := (553559113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869716425897 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869716425897 / 500000000000) = 1/(500000000000 / 869716425897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (69194889 / 125000000) (553559113 / 1000000000) (Real.log (869716425897 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (869716425897 / 500000000000) = -Real.log (500000000000 / 869716425897) := by
    rw [show ((869716425897 / 500000000000) : ℝ) = ((500000000000 / 869716425897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (386836833 / 1000000000) ≤ -Real.log (500000000000 / 736158119457) ∧
    -Real.log (500000000000 / 736158119457) ≤ (193418417 / 500000000) := by
  have h := checkLog_sound (w := (236158119457 / 1236158119457)) (n := 12)
    (lo := (386836833 / 1000000000)) (hi := (193418417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736158119457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736158119457 / 500000000000) = 1/(500000000000 / 736158119457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (386836833 / 1000000000) (193418417 / 500000000) (Real.log (736158119457 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (736158119457 / 500000000000) = -Real.log (500000000000 / 736158119457) := by
    rw [show ((736158119457 / 500000000000) : ℝ) = ((500000000000 / 736158119457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (96927181 / 250000000) ≤ -Real.log (500000000000 / 736800249339) ∧
    -Real.log (500000000000 / 736800249339) ≤ (15508349 / 40000000) := by
  have h := checkLog_sound (w := (236800249339 / 1236800249339)) (n := 12)
    (lo := (96927181 / 250000000)) (hi := (15508349 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736800249339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736800249339 / 500000000000) = 1/(500000000000 / 736800249339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (96927181 / 250000000) (15508349 / 40000000) (Real.log (736800249339 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (736800249339 / 500000000000) = -Real.log (500000000000 / 736800249339) := by
    rw [show ((736800249339 / 500000000000) : ℝ) = ((500000000000 / 736800249339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (27464953 / 100000000) ≤ -Real.log (50000000000 / 65803467619) ∧
    -Real.log (50000000000 / 65803467619) ≤ (274649531 / 1000000000) := by
  have h := checkLog_sound (w := (15803467619 / 115803467619)) (n := 12)
    (lo := (27464953 / 100000000)) (hi := (274649531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65803467619 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65803467619 / 50000000000) = 1/(50000000000 / 65803467619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (27464953 / 100000000) (274649531 / 1000000000) (Real.log (65803467619 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (65803467619 / 50000000000) = -Real.log (50000000000 / 65803467619) := by
    rw [show ((65803467619 / 50000000000) : ℝ) = ((50000000000 / 65803467619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (275275209 / 1000000000) ≤ -Real.log (500000000000 / 658446523213) ∧
    -Real.log (500000000000 / 658446523213) ≤ (27527521 / 100000000) := by
  have h := checkLog_sound (w := (158446523213 / 1158446523213)) (n := 12)
    (lo := (275275209 / 1000000000)) (hi := (27527521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658446523213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658446523213 / 500000000000) = 1/(500000000000 / 658446523213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (275275209 / 1000000000) (27527521 / 100000000) (Real.log (658446523213 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (658446523213 / 500000000000) = -Real.log (500000000000 / 658446523213) := by
    rw [show ((658446523213 / 500000000000) : ℝ) = ((500000000000 / 658446523213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18884597 / 1000000000) ≤ -Real.log (1570068159 / 1600000000) ∧
    -Real.log (1570068159 / 1600000000) ≤ (9442299 / 500000000) := by
  have h := checkLog_sound (w := (29931841 / 3170068159)) (n := 12)
    (lo := (18884597 / 1000000000)) (hi := (9442299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1570068159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1570068159) = 1/(1570068159 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9442299 / 500000000) (-18884597 / 1000000000) (Real.log (1570068159 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4699779 / 250000000) ≤ -Real.log (61336030311 / 62500000000) ∧
    -Real.log (61336030311 / 62500000000) ≤ (18799117 / 1000000000) := by
  have h := checkLog_sound (w := (1163969689 / 123836030311)) (n := 12)
    (lo := (4699779 / 250000000)) (hi := (18799117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61336030311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61336030311) = 1/(61336030311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18799117 / 1000000000) (-4699779 / 250000000) (Real.log (61336030311 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell033

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell034Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell034
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (7481771 / 31250000) ≤ -Real.log (1024 / 1301) ∧
    -Real.log (1024 / 1301) ≤ (239416673 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2325)) (n := 12)
    (lo := (7481771 / 31250000)) (hi := (239416673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301 / 1024) = 1/(1024 / 1301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (7481771 / 31250000) (239416673 / 1000000000) (Real.log (1301 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1301 / 1024) = -Real.log (1024 / 1301) := by
    rw [show ((1301 / 1024) : ℝ) = ((1024 / 1301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15770331 / 50000000) ≤ -Real.log (747 / 1024) ∧
    -Real.log (747 / 1024) ≤ (315406621 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1771)) (n := 12)
    (lo := (15770331 / 50000000)) (hi := (315406621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 747) = 1/(747 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-315406621 / 1000000000) (-15770331 / 50000000) (Real.log (747 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (119477691 / 500000000) ≤ -Real.log (2560 / 3251) ∧
    -Real.log (2560 / 3251) ≤ (238955383 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 5811)) (n := 12)
    (lo := (119477691 / 500000000)) (hi := (238955383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3251 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3251 / 2560) = 1/(2560 / 3251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (119477691 / 500000000) (238955383 / 1000000000) (Real.log (3251 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3251 / 2560) = -Real.log (2560 / 3251) := by
    rw [show ((3251 / 2560) : ℝ) = ((2560 / 3251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31460373 / 100000000) ≤ -Real.log (1869 / 2560) ∧
    -Real.log (1869 / 2560) ≤ (314603731 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 4429)) (n := 12)
    (lo := (31460373 / 100000000)) (hi := (314603731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1869) = 1/(1869 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-314603731 / 1000000000) (-31460373 / 100000000) (Real.log (1869 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35036057 / 200000000) ≤ -Real.log (1000000 / 1191461) ∧
    -Real.log (1000000 / 1191461) ≤ (87590143 / 500000000) := by
  have h := checkLog_sound (w := (191461 / 2191461)) (n := 12)
    (lo := (35036057 / 200000000)) (hi := (87590143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191461 / 1000000) = 1/(1000000 / 1191461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35036057 / 200000000) (87590143 / 500000000) (Real.log (1191461 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1191461 / 1000000) = -Real.log (1000000 / 1191461) := by
    rw [show ((1191461 / 1000000) : ℝ) = ((1000000 / 1191461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (212526363 / 1000000000) ≤ -Real.log (808539 / 1000000) ∧
    -Real.log (808539 / 1000000) ≤ (53131591 / 250000000) := by
  have h := checkLog_sound (w := (191461 / 1808539)) (n := 12)
    (lo := (212526363 / 1000000000)) (hi := (53131591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808539) = 1/(808539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-53131591 / 250000000) (-212526363 / 1000000000) (Real.log (808539 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43882973 / 250000000) ≤ -Real.log (25000 / 29797) ∧
    -Real.log (25000 / 29797) ≤ (175531893 / 1000000000) := by
  have h := checkLog_sound (w := (4797 / 54797)) (n := 12)
    (lo := (43882973 / 250000000)) (hi := (175531893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29797 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29797 / 25000) = 1/(25000 / 29797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43882973 / 250000000) (175531893 / 1000000000) (Real.log (29797 / 25000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (29797 / 25000) = -Real.log (25000 / 29797) := by
    rw [show ((29797 / 25000) : ℝ) = ((25000 / 29797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (53261179 / 250000000) ≤ -Real.log (20203 / 25000) ∧
    -Real.log (20203 / 25000) ≤ (213044717 / 1000000000) := by
  have h := checkLog_sound (w := (4797 / 45203)) (n := 12)
    (lo := (53261179 / 250000000)) (hi := (213044717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20203) = 1/(20203 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-213044717 / 1000000000) (-53261179 / 250000000) (Real.log (20203 / 25000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (64096773 / 500000000) ≤ -Real.log (1000000 / 1136773) ∧
    -Real.log (1000000 / 1136773) ≤ (128193547 / 1000000000) := by
  have h := checkLog_sound (w := (136773 / 2136773)) (n := 12)
    (lo := (64096773 / 500000000)) (hi := (128193547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136773 / 1000000) = 1/(1000000 / 1136773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (64096773 / 500000000) (128193547 / 1000000000) (Real.log (1136773 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1136773 / 1000000) = -Real.log (1000000 / 1136773) := by
    rw [show ((1136773 / 1000000) : ℝ) = ((1000000 / 1136773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73538793 / 500000000) ≤ -Real.log (863227 / 1000000) ∧
    -Real.log (863227 / 1000000) ≤ (147077587 / 1000000000) := by
  have h := checkLog_sound (w := (136773 / 1863227)) (n := 12)
    (lo := (73538793 / 500000000)) (hi := (147077587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863227) = 1/(863227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-147077587 / 1000000000) (-73538793 / 500000000) (Real.log (863227 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (128462693 / 1000000000) ≤ -Real.log (1000000 / 1137079) ∧
    -Real.log (1000000 / 1137079) ≤ (64231347 / 500000000) := by
  have h := checkLog_sound (w := (137079 / 2137079)) (n := 12)
    (lo := (128462693 / 1000000000)) (hi := (64231347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137079 / 1000000) = 1/(1000000 / 1137079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (128462693 / 1000000000) (64231347 / 500000000) (Real.log (1137079 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1137079 / 1000000) = -Real.log (1000000 / 1137079) := by
    rw [show ((1137079 / 1000000) : ℝ) = ((1000000 / 1137079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (147432133 / 1000000000) ≤ -Real.log (862921 / 1000000) ∧
    -Real.log (862921 / 1000000) ≤ (73716067 / 500000000) := by
  have h := checkLog_sound (w := (137079 / 1862921)) (n := 12)
    (lo := (147432133 / 1000000000)) (hi := (73716067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862921) = 1/(862921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-73716067 / 500000000) (-147432133 / 1000000000) (Real.log (862921 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (69194889 / 125000000) ≤ -Real.log (62500000000 / 108714553237) ∧
    -Real.log (62500000000 / 108714553237) ≤ (553559113 / 1000000000) := by
  have h := checkLog_sound (w := (46214553237 / 171214553237)) (n := 12)
    (lo := (69194889 / 125000000)) (hi := (553559113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108714553237 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108714553237 / 62500000000) = 1/(62500000000 / 108714553237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (69194889 / 125000000) (553559113 / 1000000000) (Real.log (108714553237 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (108714553237 / 62500000000) = -Real.log (62500000000 / 108714553237) := by
    rw [show ((108714553237 / 62500000000) : ℝ) = ((62500000000 / 108714553237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (554823293 / 1000000000) ≤ -Real.log (500000000000 / 870816599733) ∧
    -Real.log (500000000000 / 870816599733) ≤ (277411647 / 500000000) := by
  have h := checkLog_sound (w := (370816599733 / 1370816599733)) (n := 12)
    (lo := (554823293 / 1000000000)) (hi := (277411647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870816599733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870816599733 / 500000000000) = 1/(500000000000 / 870816599733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (554823293 / 1000000000) (277411647 / 500000000) (Real.log (870816599733 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (870816599733 / 500000000000) = -Real.log (500000000000 / 870816599733) := by
    rw [show ((870816599733 / 500000000000) : ℝ) = ((500000000000 / 870816599733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (48463331 / 125000000) ≤ -Real.log (100000000000 / 147359743933) ∧
    -Real.log (100000000000 / 147359743933) ≤ (387706649 / 1000000000) := by
  have h := checkLog_sound (w := (47359743933 / 247359743933)) (n := 12)
    (lo := (48463331 / 125000000)) (hi := (387706649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147359743933 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147359743933 / 100000000000) = 1/(100000000000 / 147359743933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48463331 / 125000000) (387706649 / 1000000000) (Real.log (147359743933 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (147359743933 / 100000000000) = -Real.log (100000000000 / 147359743933) := by
    rw [show ((147359743933 / 100000000000) : ℝ) = ((100000000000 / 147359743933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (388576609 / 1000000000) ≤ -Real.log (500000000000 / 737439984161) ∧
    -Real.log (500000000000 / 737439984161) ≤ (38857661 / 100000000) := by
  have h := checkLog_sound (w := (237439984161 / 1237439984161)) (n := 12)
    (lo := (388576609 / 1000000000)) (hi := (38857661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737439984161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737439984161 / 500000000000) = 1/(500000000000 / 737439984161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (388576609 / 1000000000) (38857661 / 100000000) (Real.log (737439984161 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (737439984161 / 500000000000) = -Real.log (500000000000 / 737439984161) := by
    rw [show ((737439984161 / 500000000000) : ℝ) = ((500000000000 / 737439984161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (275271133 / 1000000000) ≤ -Real.log (500000000000 / 658443839221) ∧
    -Real.log (500000000000 / 658443839221) ≤ (137635567 / 500000000) := by
  have h := checkLog_sound (w := (158443839221 / 1158443839221)) (n := 12)
    (lo := (275271133 / 1000000000)) (hi := (137635567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658443839221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658443839221 / 500000000000) = 1/(500000000000 / 658443839221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (275271133 / 1000000000) (137635567 / 500000000) (Real.log (658443839221 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (658443839221 / 500000000000) = -Real.log (500000000000 / 658443839221) := by
    rw [show ((658443839221 / 500000000000) : ℝ) = ((500000000000 / 658443839221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (137947413 / 500000000) ≤ -Real.log (250000000000 / 329427317217) ∧
    -Real.log (250000000000 / 329427317217) ≤ (275894827 / 1000000000) := by
  have h := checkLog_sound (w := (79427317217 / 579427317217)) (n := 12)
    (lo := (137947413 / 500000000)) (hi := (275894827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329427317217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329427317217 / 250000000000) = 1/(250000000000 / 329427317217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (137947413 / 500000000) (275894827 / 1000000000) (Real.log (329427317217 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (329427317217 / 250000000000) = -Real.log (250000000000 / 329427317217) := by
    rw [show ((329427317217 / 250000000000) : ℝ) = ((250000000000 / 329427317217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18969439 / 1000000000) ≤ -Real.log (981209347759 / 1000000000000) ∧
    -Real.log (981209347759 / 1000000000000) ≤ (118559 / 6250000) := by
  have h := checkLog_sound (w := (18790652241 / 1981209347759)) (n := 12)
    (lo := (18969439 / 1000000000)) (hi := (118559 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981209347759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981209347759) = 1/(981209347759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-118559 / 6250000) (-18969439 / 1000000000) (Real.log (981209347759 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18884039 / 1000000000) ≤ -Real.log (981293146471 / 1000000000000) ∧
    -Real.log (981293146471 / 1000000000000) ≤ (472101 / 25000000) := by
  have h := checkLog_sound (w := (18706853529 / 1981293146471)) (n := 12)
    (lo := (18884039 / 1000000000)) (hi := (472101 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981293146471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981293146471) = 1/(981293146471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-472101 / 25000000) (-18884039 / 1000000000) (Real.log (981293146471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell034

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell035Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell035
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (959511 / 4000000) ≤ -Real.log (1280 / 1627) ∧
    -Real.log (1280 / 1627) ≤ (239877751 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2907)) (n := 12)
    (lo := (959511 / 4000000)) (hi := (239877751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1627 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1627 / 1280) = 1/(1280 / 1627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (959511 / 4000000) (239877751 / 1000000000) (Real.log (1627 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1627 / 1280) = -Real.log (1280 / 1627) := by
    rw [show ((1627 / 1280) : ℝ) = ((1280 / 1627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (79052539 / 250000000) ≤ -Real.log (933 / 1280) ∧
    -Real.log (933 / 1280) ≤ (316210157 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2213)) (n := 12)
    (lo := (79052539 / 250000000)) (hi := (316210157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 933) = 1/(933 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-316210157 / 1000000000) (-79052539 / 250000000) (Real.log (933 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (7481771 / 31250000) ≤ -Real.log (1024 / 1301) ∧
    -Real.log (1024 / 1301) ≤ (239416673 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2325)) (n := 12)
    (lo := (7481771 / 31250000)) (hi := (239416673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301 / 1024) = 1/(1024 / 1301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (7481771 / 31250000) (239416673 / 1000000000) (Real.log (1301 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1301 / 1024) = -Real.log (1024 / 1301) := by
    rw [show ((1301 / 1024) : ℝ) = ((1024 / 1301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15770331 / 50000000) ≤ -Real.log (747 / 1024) ∧
    -Real.log (747 / 1024) ≤ (315406621 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1771)) (n := 12)
    (lo := (15770331 / 50000000)) (hi := (315406621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 747) = 1/(747 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-315406621 / 1000000000) (-15770331 / 50000000) (Real.log (747 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (175531053 / 1000000000) ≤ -Real.log (1000000 / 1191879) ∧
    -Real.log (1000000 / 1191879) ≤ (87765527 / 500000000) := by
  have h := checkLog_sound (w := (191879 / 2191879)) (n := 12)
    (lo := (175531053 / 1000000000)) (hi := (87765527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191879 / 1000000) = 1/(1000000 / 1191879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (175531053 / 1000000000) (87765527 / 500000000) (Real.log (1191879 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1191879 / 1000000) = -Real.log (1000000 / 1191879) := by
    rw [show ((1191879 / 1000000) : ℝ) = ((1000000 / 1191879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (213043479 / 1000000000) ≤ -Real.log (808121 / 1000000) ∧
    -Real.log (808121 / 1000000) ≤ (5326087 / 25000000) := by
  have h := checkLog_sound (w := (191879 / 1808121)) (n := 12)
    (lo := (213043479 / 1000000000)) (hi := (5326087 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808121) = 1/(808121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5326087 / 25000000) (-213043479 / 1000000000) (Real.log (808121 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (175882537 / 1000000000) ≤ -Real.log (500000 / 596149) ∧
    -Real.log (500000 / 596149) ≤ (87941269 / 500000000) := by
  have h := checkLog_sound (w := (96149 / 1096149)) (n := 12)
    (lo := (175882537 / 1000000000)) (hi := (87941269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596149 / 500000) = 1/(500000 / 596149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (175882537 / 1000000000) (87941269 / 500000000) (Real.log (596149 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (596149 / 500000) = -Real.log (500000 / 596149) := by
    rw [show ((596149 / 500000) : ℝ) = ((500000 / 596149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2135621 / 10000000) ≤ -Real.log (403851 / 500000) ∧
    -Real.log (403851 / 500000) ≤ (213562101 / 1000000000) := by
  have h := checkLog_sound (w := (96149 / 903851)) (n := 12)
    (lo := (2135621 / 10000000)) (hi := (213562101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403851) = 1/(403851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-213562101 / 1000000000) (-2135621 / 10000000) (Real.log (403851 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128461813 / 1000000000) ≤ -Real.log (500000 / 568539) ∧
    -Real.log (500000 / 568539) ≤ (64230907 / 500000000) := by
  have h := checkLog_sound (w := (68539 / 1068539)) (n := 12)
    (lo := (128461813 / 1000000000)) (hi := (64230907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568539 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(568539 / 500000) = 1/(500000 / 568539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128461813 / 1000000000) (64230907 / 500000000) (Real.log (568539 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (568539 / 500000) = -Real.log (500000 / 568539) := by
    rw [show ((568539 / 500000) : ℝ) = ((500000 / 568539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73715487 / 500000000) ≤ -Real.log (431461 / 500000) ∧
    -Real.log (431461 / 500000) ≤ (5897239 / 40000000) := by
  have h := checkLog_sound (w := (68539 / 931461)) (n := 12)
    (lo := (73715487 / 500000000)) (hi := (5897239 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 431461) = 1/(431461 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5897239 / 40000000) (-73715487 / 500000000) (Real.log (431461 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16091361 / 125000000) ≤ -Real.log (125000 / 142173) ∧
    -Real.log (125000 / 142173) ≤ (128730889 / 1000000000) := by
  have h := checkLog_sound (w := (17173 / 267173)) (n := 12)
    (lo := (16091361 / 125000000)) (hi := (128730889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142173 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142173 / 125000) = 1/(125000 / 142173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16091361 / 125000000) (128730889 / 1000000000) (Real.log (142173 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142173 / 125000) = -Real.log (125000 / 142173) := by
    rw [show ((142173 / 125000) : ℝ) = ((125000 / 142173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73892823 / 500000000) ≤ -Real.log (107827 / 125000) ∧
    -Real.log (107827 / 125000) ≤ (147785647 / 1000000000) := by
  have h := checkLog_sound (w := (17173 / 232827)) (n := 12)
    (lo := (73892823 / 500000000)) (hi := (147785647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107827) = 1/(107827 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-147785647 / 1000000000) (-73892823 / 500000000) (Real.log (107827 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (554823293 / 1000000000) ≤ -Real.log (125000000000 / 217704149933) ∧
    -Real.log (125000000000 / 217704149933) ≤ (277411647 / 500000000) := by
  have h := checkLog_sound (w := (92704149933 / 342704149933)) (n := 12)
    (lo := (554823293 / 1000000000)) (hi := (277411647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217704149933 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217704149933 / 125000000000) = 1/(125000000000 / 217704149933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (554823293 / 1000000000) (277411647 / 500000000) (Real.log (217704149933 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (217704149933 / 125000000000) = -Real.log (125000000000 / 217704149933) := by
    rw [show ((217704149933 / 125000000000) : ℝ) = ((125000000000 / 217704149933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (278043953 / 500000000) ≤ -Real.log (500000000000 / 871918542337) ∧
    -Real.log (500000000000 / 871918542337) ≤ (556087907 / 1000000000) := by
  have h := checkLog_sound (w := (371918542337 / 1371918542337)) (n := 12)
    (lo := (278043953 / 500000000)) (hi := (556087907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871918542337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871918542337 / 500000000000) = 1/(500000000000 / 871918542337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (278043953 / 500000000) (556087907 / 1000000000) (Real.log (871918542337 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (871918542337 / 500000000000) = -Real.log (500000000000 / 871918542337) := by
    rw [show ((871918542337 / 500000000000) : ℝ) = ((500000000000 / 871918542337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (97143633 / 250000000) ≤ -Real.log (62500000000 / 92179806613) ∧
    -Real.log (62500000000 / 92179806613) ≤ (388574533 / 1000000000) := by
  have h := checkLog_sound (w := (29679806613 / 154679806613)) (n := 12)
    (lo := (97143633 / 250000000)) (hi := (388574533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92179806613 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92179806613 / 62500000000) = 1/(62500000000 / 92179806613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97143633 / 250000000) (388574533 / 1000000000) (Real.log (92179806613 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (92179806613 / 62500000000) = -Real.log (62500000000 / 92179806613) := by
    rw [show ((92179806613 / 62500000000) : ℝ) = ((62500000000 / 92179806613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (389444637 / 1000000000) ≤ -Real.log (500000000000 / 738080381131) ∧
    -Real.log (500000000000 / 738080381131) ≤ (194722319 / 500000000) := by
  have h := checkLog_sound (w := (238080381131 / 1238080381131)) (n := 12)
    (lo := (389444637 / 1000000000)) (hi := (194722319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738080381131 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738080381131 / 500000000000) = 1/(500000000000 / 738080381131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (389444637 / 1000000000) (194722319 / 500000000) (Real.log (738080381131 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (738080381131 / 500000000000) = -Real.log (500000000000 / 738080381131) := by
    rw [show ((738080381131 / 500000000000) : ℝ) = ((500000000000 / 738080381131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (68973197 / 250000000) ≤ -Real.log (500000000000 / 658853291491) ∧
    -Real.log (500000000000 / 658853291491) ≤ (275892789 / 1000000000) := by
  have h := checkLog_sound (w := (158853291491 / 1158853291491)) (n := 12)
    (lo := (68973197 / 250000000)) (hi := (275892789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658853291491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658853291491 / 500000000000) = 1/(500000000000 / 658853291491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (68973197 / 250000000) (275892789 / 1000000000) (Real.log (658853291491 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (658853291491 / 500000000000) = -Real.log (500000000000 / 658853291491) := by
    rw [show ((658853291491 / 500000000000) : ℝ) = ((500000000000 / 658853291491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (138258267 / 500000000) ≤ -Real.log (500000000000 / 659264377197) ∧
    -Real.log (500000000000 / 659264377197) ≤ (55303307 / 200000000) := by
  have h := checkLog_sound (w := (159264377197 / 1159264377197)) (n := 12)
    (lo := (138258267 / 500000000)) (hi := (55303307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659264377197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659264377197 / 500000000000) = 1/(500000000000 / 659264377197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (138258267 / 500000000) (55303307 / 200000000) (Real.log (659264377197 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (659264377197 / 500000000000) = -Real.log (500000000000 / 659264377197) := by
    rw [show ((659264377197 / 500000000000) : ℝ) = ((500000000000 / 659264377197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19054757 / 1000000000) ≤ -Real.log (15330088071 / 15625000000) ∧
    -Real.log (15330088071 / 15625000000) ≤ (9527379 / 500000000) := by
  have h := checkLog_sound (w := (294911929 / 30955088071)) (n := 12)
    (lo := (19054757 / 1000000000)) (hi := (9527379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15330088071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15330088071) = 1/(15330088071 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9527379 / 500000000) (-19054757 / 1000000000) (Real.log (15330088071 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (474229 / 25000000) ≤ -Real.log (245302405479 / 250000000000) ∧
    -Real.log (245302405479 / 250000000000) ≤ (18969161 / 1000000000) := by
  have h := checkLog_sound (w := (4697594521 / 495302405479)) (n := 12)
    (lo := (474229 / 25000000)) (hi := (18969161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245302405479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245302405479) = 1/(245302405479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18969161 / 1000000000) (-474229 / 25000000) (Real.log (245302405479 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell035

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell036Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell036
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (48067723 / 200000000) ≤ -Real.log (5120 / 6511) ∧
    -Real.log (5120 / 6511) ≤ (30042327 / 125000000) := by
  have h := checkLog_sound (w := (1391 / 11631)) (n := 12)
    (lo := (48067723 / 200000000)) (hi := (30042327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6511 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6511 / 5120) = 1/(5120 / 6511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (48067723 / 200000000) (30042327 / 125000000) (Real.log (6511 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6511 / 5120) = -Real.log (5120 / 6511) := by
    rw [show ((6511 / 5120) : ℝ) = ((5120 / 6511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (317014337 / 1000000000) ≤ -Real.log (3729 / 5120) ∧
    -Real.log (3729 / 5120) ≤ (158507169 / 500000000) := by
  have h := checkLog_sound (w := (1391 / 8849)) (n := 12)
    (lo := (317014337 / 1000000000)) (hi := (158507169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3729) = 1/(3729 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-158507169 / 500000000) (-317014337 / 1000000000) (Real.log (3729 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (959511 / 4000000) ≤ -Real.log (1280 / 1627) ∧
    -Real.log (1280 / 1627) ≤ (239877751 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2907)) (n := 12)
    (lo := (959511 / 4000000)) (hi := (239877751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1627 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1627 / 1280) = 1/(1280 / 1627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (959511 / 4000000) (239877751 / 1000000000) (Real.log (1627 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1627 / 1280) = -Real.log (1280 / 1627) := by
    rw [show ((1627 / 1280) : ℝ) = ((1280 / 1627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (79052539 / 250000000) ≤ -Real.log (933 / 1280) ∧
    -Real.log (933 / 1280) ≤ (316210157 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2213)) (n := 12)
    (lo := (79052539 / 250000000)) (hi := (316210157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 933) = 1/(933 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-316210157 / 1000000000) (-79052539 / 250000000) (Real.log (933 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87940849 / 500000000) ≤ -Real.log (1000000 / 1192297) ∧
    -Real.log (1000000 / 1192297) ≤ (175881699 / 1000000000) := by
  have h := checkLog_sound (w := (192297 / 2192297)) (n := 12)
    (lo := (87940849 / 500000000)) (hi := (175881699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192297 / 1000000) = 1/(1000000 / 1192297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87940849 / 500000000) (175881699 / 1000000000) (Real.log (1192297 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1192297 / 1000000) = -Real.log (1000000 / 1192297) := by
    rw [show ((1192297 / 1000000) : ℝ) = ((1000000 / 1192297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (106780431 / 500000000) ≤ -Real.log (807703 / 1000000) ∧
    -Real.log (807703 / 1000000) ≤ (213560863 / 1000000000) := by
  have h := checkLog_sound (w := (192297 / 1807703)) (n := 12)
    (lo := (106780431 / 500000000)) (hi := (213560863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807703) = 1/(807703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-213560863 / 1000000000) (-106780431 / 500000000) (Real.log (807703 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (176233897 / 1000000000) ≤ -Real.log (1000000 / 1192717) ∧
    -Real.log (1000000 / 1192717) ≤ (88116949 / 500000000) := by
  have h := checkLog_sound (w := (192717 / 2192717)) (n := 12)
    (lo := (176233897 / 1000000000)) (hi := (88116949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192717 / 1000000) = 1/(1000000 / 1192717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (176233897 / 1000000000) (88116949 / 500000000) (Real.log (1192717 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1192717 / 1000000) = -Real.log (1000000 / 1192717) := by
    rw [show ((1192717 / 1000000) : ℝ) = ((1000000 / 1192717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (21408099 / 100000000) ≤ -Real.log (807283 / 1000000) ∧
    -Real.log (807283 / 1000000) ≤ (214080991 / 1000000000) := by
  have h := checkLog_sound (w := (192717 / 1807283)) (n := 12)
    (lo := (21408099 / 100000000)) (hi := (214080991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807283) = 1/(807283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-214080991 / 1000000000) (-21408099 / 100000000) (Real.log (807283 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128730009 / 1000000000) ≤ -Real.log (1000000 / 1137383) ∧
    -Real.log (1000000 / 1137383) ≤ (12873001 / 100000000) := by
  have h := checkLog_sound (w := (137383 / 2137383)) (n := 12)
    (lo := (128730009 / 1000000000)) (hi := (12873001 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137383 / 1000000) = 1/(1000000 / 1137383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128730009 / 1000000000) (12873001 / 100000000) (Real.log (1137383 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1137383 / 1000000) = -Real.log (1000000 / 1137383) := by
    rw [show ((1137383 / 1000000) : ℝ) = ((1000000 / 1137383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (147784487 / 1000000000) ≤ -Real.log (862617 / 1000000) ∧
    -Real.log (862617 / 1000000) ≤ (18473061 / 125000000) := by
  have h := checkLog_sound (w := (137383 / 1862617)) (n := 12)
    (lo := (147784487 / 1000000000)) (hi := (18473061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862617) = 1/(862617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18473061 / 125000000) (-147784487 / 1000000000) (Real.log (862617 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (128999011 / 1000000000) ≤ -Real.log (1000000 / 1137689) ∧
    -Real.log (1000000 / 1137689) ≤ (32249753 / 250000000) := by
  have h := checkLog_sound (w := (137689 / 2137689)) (n := 12)
    (lo := (128999011 / 1000000000)) (hi := (32249753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137689 / 1000000) = 1/(1000000 / 1137689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (128999011 / 1000000000) (32249753 / 250000000) (Real.log (1137689 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1137689 / 1000000) = -Real.log (1000000 / 1137689) := by
    rw [show ((1137689 / 1000000) : ℝ) = ((1000000 / 1137689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (37034821 / 250000000) ≤ -Real.log (862311 / 1000000) ∧
    -Real.log (862311 / 1000000) ≤ (29627857 / 200000000) := by
  have h := checkLog_sound (w := (137689 / 1862311)) (n := 12)
    (lo := (37034821 / 250000000)) (hi := (29627857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862311) = 1/(862311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-29627857 / 200000000) (-37034821 / 250000000) (Real.log (862311 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (278043953 / 500000000) ≤ -Real.log (976562500 / 1702965903) ∧
    -Real.log (976562500 / 1702965903) ≤ (556087907 / 1000000000) := by
  have h := checkLog_sound (w := (726403403 / 2679528403)) (n := 12)
    (lo := (278043953 / 500000000)) (hi := (556087907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1702965903 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1702965903 / 976562500) = 1/(976562500 / 1702965903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (278043953 / 500000000) (556087907 / 1000000000) (Real.log (1702965903 / 976562500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1702965903 / 976562500) = -Real.log (976562500 / 1702965903) := by
    rw [show ((1702965903 / 976562500) : ℝ) = ((976562500 / 1702965903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (557352953 / 1000000000) ≤ -Real.log (500000000000 / 873022257979) ∧
    -Real.log (500000000000 / 873022257979) ≤ (278676477 / 500000000) := by
  have h := checkLog_sound (w := (373022257979 / 1373022257979)) (n := 12)
    (lo := (557352953 / 1000000000)) (hi := (278676477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873022257979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873022257979 / 500000000000) = 1/(500000000000 / 873022257979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (557352953 / 1000000000) (278676477 / 500000000) (Real.log (873022257979 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (873022257979 / 500000000000) = -Real.log (500000000000 / 873022257979) := by
    rw [show ((873022257979 / 500000000000) : ℝ) = ((500000000000 / 873022257979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (152126 / 390625) ≤ -Real.log (500000000000 / 738078848289) ∧
    -Real.log (500000000000 / 738078848289) ≤ (389442561 / 1000000000) := by
  have h := checkLog_sound (w := (238078848289 / 1238078848289)) (n := 12)
    (lo := (152126 / 390625)) (hi := (389442561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738078848289 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738078848289 / 500000000000) = 1/(500000000000 / 738078848289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (152126 / 390625) (389442561 / 1000000000) (Real.log (738078848289 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (738078848289 / 500000000000) = -Real.log (500000000000 / 738078848289) := by
    rw [show ((738078848289 / 500000000000) : ℝ) = ((500000000000 / 738078848289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48789361 / 125000000) ≤ -Real.log (50000000000 / 73872297571) ∧
    -Real.log (50000000000 / 73872297571) ≤ (390314889 / 1000000000) := by
  have h := checkLog_sound (w := (23872297571 / 123872297571)) (n := 12)
    (lo := (48789361 / 125000000)) (hi := (390314889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73872297571 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73872297571 / 50000000000) = 1/(50000000000 / 73872297571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (48789361 / 125000000) (390314889 / 1000000000) (Real.log (73872297571 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (73872297571 / 50000000000) = -Real.log (50000000000 / 73872297571) := by
    rw [show ((73872297571 / 50000000000) : ℝ) = ((50000000000 / 73872297571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (4320539 / 15625000) ≤ -Real.log (62500000000 / 82407879163) ∧
    -Real.log (62500000000 / 82407879163) ≤ (276514497 / 1000000000) := by
  have h := checkLog_sound (w := (19907879163 / 144907879163)) (n := 12)
    (lo := (4320539 / 15625000)) (hi := (276514497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82407879163 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82407879163 / 62500000000) = 1/(62500000000 / 82407879163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4320539 / 15625000) (276514497 / 1000000000) (Real.log (82407879163 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82407879163 / 62500000000) = -Real.log (62500000000 / 82407879163) := by
    rw [show ((82407879163 / 62500000000) : ℝ) = ((62500000000 / 82407879163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34642287 / 125000000) ≤ -Real.log (500000000000 / 659674409813) ∧
    -Real.log (500000000000 / 659674409813) ≤ (277138297 / 1000000000) := by
  have h := checkLog_sound (w := (159674409813 / 1159674409813)) (n := 12)
    (lo := (34642287 / 125000000)) (hi := (277138297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659674409813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659674409813 / 500000000000) = 1/(500000000000 / 659674409813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34642287 / 125000000) (277138297 / 1000000000) (Real.log (659674409813 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (659674409813 / 500000000000) = -Real.log (500000000000 / 659674409813) := by
    rw [show ((659674409813 / 500000000000) : ℝ) = ((500000000000 / 659674409813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1196267 / 62500000) ≤ -Real.log (981041739279 / 1000000000000) ∧
    -Real.log (981041739279 / 1000000000000) ≤ (19140273 / 1000000000) := by
  have h := checkLog_sound (w := (18958260721 / 1981041739279)) (n := 12)
    (lo := (1196267 / 62500000)) (hi := (19140273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981041739279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981041739279) = 1/(981041739279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19140273 / 1000000000) (-1196267 / 62500000) (Real.log (981041739279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19054477 / 1000000000) ≤ -Real.log (981125911311 / 1000000000000) ∧
    -Real.log (981125911311 / 1000000000000) ≤ (9527239 / 500000000) := by
  have h := checkLog_sound (w := (18874088689 / 1981125911311)) (n := 12)
    (lo := (19054477 / 1000000000)) (hi := (9527239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981125911311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981125911311) = 1/(981125911311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9527239 / 500000000) (-19054477 / 1000000000) (Real.log (981125911311 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell036

end


