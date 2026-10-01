-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0010Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0010Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:07:40.694977+00:00
-- url     : https://prove2.me/theorems/e7c4bbf0-bcd6-465a-92e2-727a05070ce4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0012Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0013Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0014Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0015Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0012Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0013Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0014Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0015Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0012Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0013Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0014Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0015Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0010Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0011Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0012Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0013Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0014Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0015Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0010
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

theorem reflection_log_1_neg : (101366277 / 250000000) ≤ -Real.log (2 / 3) ∧
    -Real.log (2 / 3) ≤ (405465109 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3 / 2) = 1/(2 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (101366277 / 250000000) (405465109 / 1000000000) (Real.log (3 / 2)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show ((3 / 2) : ℝ) = ((2 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
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


theorem reflection_log_2 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) (Real.log (1 / 2)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (202537203 / 500000000) ≤ -Real.log (5120 / 7677) ∧
    -Real.log (5120 / 7677) ≤ (405074407 / 1000000000) := by
  have h := checkLog_sound (w := (2557 / 12797)) (n := 12)
    (lo := (202537203 / 500000000)) (hi := (405074407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7677 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7677 / 5120) = 1/(5120 / 7677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (202537203 / 500000000) (405074407 / 1000000000) (Real.log (7677 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7677 / 5120) = -Real.log (5120 / 7677) := by
    rw [show ((7677 / 5120) : ℝ) = ((5120 / 7677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (691975991 / 1000000000) ≤ -Real.log (2563 / 5120) ∧
    -Real.log (2563 / 5120) ≤ (86496999 / 125000000) := by
  have h := checkLog_sound (w := (2557 / 7683)) (n := 12)
    (lo := (691975991 / 1000000000)) (hi := (86496999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2563) = 1/(2563 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-86496999 / 125000000) (-691975991 / 1000000000) (Real.log (2563 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (692561071 / 1000000000) ≤ -Real.log (2560 / 5117) ∧
    -Real.log (2560 / 5117) ≤ (43285067 / 62500000) := by
  have h := checkLog_sound (w := (2557 / 7677)) (n := 12)
    (lo := (692561071 / 1000000000)) (hi := (43285067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5117 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5117 / 2560) = 1/(2560 / 5117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (692561071 / 1000000000) (43285067 / 62500000) (Real.log (5117 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5117 / 2560) = -Real.log (2560 / 5117) := by
    rw [show ((5117 / 2560) : ℝ) = ((2560 / 5117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6749150243 / 1000000000) ≤ -Real.log (3 / 2560) ∧
    -Real.log (3 / 2560) ≤ (6749150253 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(5 / 3) = 1/(3 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6749150253 / 1000000000) (-6749150243 / 1000000000) (Real.log (3 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23009913 / 40000000) ≤ -Real.log (1000000 / 1777571) ∧
    -Real.log (1000000 / 1777571) ≤ (287623913 / 500000000) := by
  have h := checkLog_sound (w := (777571 / 2777571)) (n := 12)
    (lo := (23009913 / 40000000)) (hi := (287623913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777571 / 1000000) = 1/(1000000 / 1777571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23009913 / 40000000) (287623913 / 500000000) (Real.log (1777571 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1777571 / 1000000) = -Real.log (1000000 / 1777571) := by
    rw [show ((1777571 / 1000000) : ℝ) = ((1000000 / 1777571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23486677 / 15625000) ≤ -Real.log (222429 / 1000000) ∧
    -Real.log (222429 / 1000000) ≤ (1503147331 / 1000000000) := by
  have h := checkLog_sound (w := (27571 / 472429)) (n := 12)
    (lo := (14606621 / 125000000)) (hi := (116852969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222429) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 222429) = 1/(222429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1503147331 / 1000000000) (-23486677 / 15625000) (Real.log (222429 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9009101 / 15625000) ≤ -Real.log (200000 / 355989) ∧
    -Real.log (200000 / 355989) ≤ (115316493 / 200000000) := by
  have h := checkLog_sound (w := (155989 / 555989)) (n := 12)
    (lo := (9009101 / 15625000)) (hi := (115316493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355989 / 200000) = 1/(200000 / 355989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9009101 / 15625000) (115316493 / 200000000) (Real.log (355989 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (355989 / 200000) = -Real.log (200000 / 355989) := by
    rw [show ((355989 / 200000) : ℝ) = ((200000 / 355989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (756938881 / 500000000) ≤ -Real.log (44011 / 200000) ∧
    -Real.log (44011 / 200000) ≤ (302775553 / 200000000) := by
  have h := checkLog_sound (w := (5989 / 94011)) (n := 12)
    (lo := (63791701 / 500000000)) (hi := (127583403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44011) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 44011) = 1/(44011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-302775553 / 200000000) (-756938881 / 500000000) (Real.log (44011 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4037047 / 8000000) ≤ -Real.log (500000 / 828187) ∧
    -Real.log (500000 / 828187) ≤ (126157719 / 250000000) := by
  have h := checkLog_sound (w := (328187 / 1328187)) (n := 12)
    (lo := (4037047 / 8000000)) (hi := (126157719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(828187 / 500000) = 1/(500000 / 828187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4037047 / 8000000) (126157719 / 250000000) (Real.log (828187 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (828187 / 500000) = -Real.log (500000 / 828187) := by
    rw [show ((828187 / 500000) : ℝ) = ((500000 / 828187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1068201421 / 1000000000) ≤ -Real.log (171813 / 500000) ∧
    -Real.log (171813 / 500000) ≤ (1068201423 / 1000000000) := by
  have h := checkLog_sound (w := (78187 / 421813)) (n := 12)
    (lo := (375054241 / 1000000000)) (hi := (187527121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171813) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 171813) = 1/(171813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1068201423 / 1000000000) (-1068201421 / 1000000000) (Real.log (171813 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (506172213 / 1000000000) ≤ -Real.log (1000000 / 1658929) ∧
    -Real.log (1000000 / 1658929) ≤ (253086107 / 500000000) := by
  have h := checkLog_sound (w := (658929 / 2658929)) (n := 12)
    (lo := (506172213 / 1000000000)) (hi := (253086107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1658929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1658929 / 1000000) = 1/(1000000 / 1658929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (506172213 / 1000000000) (253086107 / 500000000) (Real.log (1658929 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1658929 / 1000000) = -Real.log (1000000 / 1658929) := by
    rw [show ((1658929 / 1000000) : ℝ) = ((1000000 / 1658929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1075664611 / 1000000000) ≤ -Real.log (341071 / 1000000) ∧
    -Real.log (341071 / 1000000) ≤ (1075664613 / 1000000000) := by
  have h := checkLog_sound (w := (158929 / 841071)) (n := 12)
    (lo := (382517431 / 1000000000)) (hi := (47814679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341071) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 341071) = 1/(341071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1075664613 / 1000000000) (-1075664611 / 1000000000) (Real.log (341071 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2078395153 / 1000000000) ≤ -Real.log (250000000000 / 1997908321307) ∧
    -Real.log (250000000000 / 1997908321307) ≤ (519598789 / 250000000) := by
  have h := checkLog_sound (w := (997908321307 / 2997908321307)) (n := 12)
    (lo := (692100793 / 1000000000)) (hi := (346050397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1997908321307 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1997908321307 / 1000000000000) = 1/(250000000000 / 1997908321307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2078395153 / 1000000000) (519598789 / 250000000) (Real.log (1997908321307 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1997908321307 / 250000000000) = -Real.log (250000000000 / 1997908321307) := by
    rw [show ((1997908321307 / 250000000000) : ℝ) = ((250000000000 / 1997908321307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2090460227 / 1000000000) ≤ -Real.log (500000000000 / 4044318465839) ∧
    -Real.log (500000000000 / 4044318465839) ≤ (2090460231 / 1000000000) := by
  have h := checkLog_sound (w := (44318465839 / 8044318465839)) (n := 12)
    (lo := (11018687 / 1000000000)) (hi := (172167 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4044318465839 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4044318465839 / 4000000000000) = 1/(500000000000 / 4044318465839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (2090460227 / 1000000000) (2090460231 / 1000000000) (Real.log (4044318465839 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (4044318465839 / 500000000000) = -Real.log (500000000000 / 4044318465839) := by
    rw [show ((4044318465839 / 500000000000) : ℝ) = ((500000000000 / 4044318465839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (1572832297 / 1000000000) ≤ -Real.log (2500000000 / 12050703381) ∧
    -Real.log (2500000000 / 12050703381) ≤ (15728323 / 10000000) := by
  have h := checkLog_sound (w := (2050703381 / 22050703381)) (n := 12)
    (lo := (186537937 / 1000000000)) (hi := (93268969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12050703381 / 10000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12050703381 / 10000000000) = 1/(2500000000 / 12050703381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1572832297 / 1000000000) (15728323 / 10000000) (Real.log (12050703381 / 2500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12050703381 / 2500000000) = -Real.log (2500000000 / 12050703381) := by
    rw [show ((12050703381 / 2500000000) : ℝ) = ((2500000000 / 12050703381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (197729603 / 125000000) ≤ -Real.log (50000000000 / 243194085689) ∧
    -Real.log (50000000000 / 243194085689) ≤ (1581836827 / 1000000000) := by
  have h := checkLog_sound (w := (43194085689 / 443194085689)) (n := 12)
    (lo := (3055351 / 15625000)) (hi := (39108493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243194085689 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(243194085689 / 200000000000) = 1/(50000000000 / 243194085689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (197729603 / 125000000) (1581836827 / 1000000000) (Real.log (243194085689 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (243194085689 / 50000000000) = -Real.log (50000000000 / 243194085689) := by
    rw [show ((243194085689 / 50000000000) : ℝ) = ((50000000000 / 243194085689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0010

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0011
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

theorem reflection_log_1_neg : (202537203 / 500000000) ≤ -Real.log (5120 / 7677) ∧
    -Real.log (5120 / 7677) ≤ (405074407 / 1000000000) := by
  have h := checkLog_sound (w := (2557 / 12797)) (n := 12)
    (lo := (202537203 / 500000000)) (hi := (405074407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7677 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7677 / 5120) = 1/(5120 / 7677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (202537203 / 500000000) (405074407 / 1000000000) (Real.log (7677 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7677 / 5120) = -Real.log (5120 / 7677) := by
    rw [show ((7677 / 5120) : ℝ) = ((5120 / 7677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (691975991 / 1000000000) ≤ -Real.log (2563 / 5120) ∧
    -Real.log (2563 / 5120) ≤ (86496999 / 125000000) := by
  have h := checkLog_sound (w := (2557 / 7683)) (n := 12)
    (lo := (691975991 / 1000000000)) (hi := (86496999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2563) = 1/(2563 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-86496999 / 125000000) (-691975991 / 1000000000) (Real.log (2563 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12646361 / 31250000) ≤ -Real.log (2560 / 3837) ∧
    -Real.log (2560 / 3837) ≤ (404683553 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 6397)) (n := 12)
    (lo := (12646361 / 31250000)) (hi := (404683553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3837 / 2560) = 1/(2560 / 3837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12646361 / 31250000) (404683553 / 1000000000) (Real.log (3837 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3837 / 2560) = -Real.log (2560 / 3837) := by
    rw [show ((3837 / 2560) : ℝ) = ((2560 / 3837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (172701543 / 250000000) ≤ -Real.log (1283 / 2560) ∧
    -Real.log (1283 / 2560) ≤ (690806173 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3843)) (n := 12)
    (lo := (172701543 / 250000000)) (hi := (690806173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1283) = 1/(1283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-690806173 / 1000000000) (-172701543 / 250000000) (Real.log (1283 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (692561071 / 1000000000) ≤ -Real.log (2560 / 5117) ∧
    -Real.log (2560 / 5117) ≤ (43285067 / 62500000) := by
  have h := checkLog_sound (w := (2557 / 7677)) (n := 12)
    (lo := (692561071 / 1000000000)) (hi := (43285067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5117 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5117 / 2560) = 1/(2560 / 5117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (692561071 / 1000000000) (43285067 / 62500000) (Real.log (5117 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5117 / 2560) = -Real.log (2560 / 5117) := by
    rw [show ((5117 / 2560) : ℝ) = ((2560 / 5117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6749150243 / 1000000000) ≤ -Real.log (3 / 2560) ∧
    -Real.log (3 / 2560) ≤ (6749150253 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(5 / 3) = 1/(3 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6749150253 / 1000000000) (-6749150243 / 1000000000) (Real.log (3 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (345987309 / 500000000) ≤ -Real.log (1280 / 2557) ∧
    -Real.log (1280 / 2557) ≤ (691974619 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3837)) (n := 12)
    (lo := (345987309 / 500000000)) (hi := (691974619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2557 / 1280) = 1/(1280 / 2557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (345987309 / 500000000) (691974619 / 1000000000) (Real.log (2557 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2557 / 1280) = -Real.log (1280 / 2557) := by
    rw [show ((2557 / 1280) : ℝ) = ((1280 / 2557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6056003063 / 1000000000) ≤ -Real.log (3 / 1280) ∧
    -Real.log (3 / 1280) ≤ (11828131 / 1953125) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(5 / 3) = 1/(3 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-11828131 / 1953125) (-6056003063 / 1000000000) (Real.log (3 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (897071 / 1562500) ≤ -Real.log (1000000 / 1775577) ∧
    -Real.log (1000000 / 1775577) ≤ (574125441 / 1000000000) := by
  have h := checkLog_sound (w := (775577 / 2775577)) (n := 12)
    (lo := (897071 / 1562500)) (hi := (574125441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1775577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1775577 / 1000000) = 1/(1000000 / 1775577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (897071 / 1562500) (574125441 / 1000000000) (Real.log (1775577 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1775577 / 1000000) = -Real.log (1000000 / 1775577) := by
    rw [show ((1775577 / 1000000) : ℝ) = ((1000000 / 1775577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1494222613 / 1000000000) ≤ -Real.log (224423 / 1000000) ∧
    -Real.log (224423 / 1000000) ≤ (186777827 / 125000000) := by
  have h := checkLog_sound (w := (25577 / 474423)) (n := 12)
    (lo := (107928253 / 1000000000)) (hi := (53964127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 224423) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 224423) = 1/(224423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-186777827 / 125000000) (-1494222613 / 1000000000) (Real.log (224423 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143812097 / 250000000) ≤ -Real.log (250000 / 444393) ∧
    -Real.log (250000 / 444393) ≤ (575248389 / 1000000000) := by
  have h := checkLog_sound (w := (194393 / 694393)) (n := 12)
    (lo := (143812097 / 250000000)) (hi := (575248389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444393 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444393 / 250000) = 1/(250000 / 444393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143812097 / 250000000) (575248389 / 1000000000) (Real.log (444393 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (444393 / 250000) = -Real.log (250000 / 444393) := by
    rw [show ((444393 / 250000) : ℝ) = ((250000 / 444393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93946989 / 62500000) ≤ -Real.log (55607 / 250000) ∧
    -Real.log (55607 / 250000) ≤ (1503151827 / 1000000000) := by
  have h := checkLog_sound (w := (6893 / 118107)) (n := 12)
    (lo := (14607183 / 125000000)) (hi := (23371493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55607) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 55607) = 1/(55607 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1503151827 / 1000000000) (-93946989 / 62500000) (Real.log (55607 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12582711 / 25000000) ≤ -Real.log (200000 / 330837) ∧
    -Real.log (200000 / 330837) ≤ (503308441 / 1000000000) := by
  have h := checkLog_sound (w := (130837 / 530837)) (n := 12)
    (lo := (12582711 / 25000000)) (hi := (503308441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330837 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330837 / 200000) = 1/(200000 / 330837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12582711 / 25000000) (503308441 / 1000000000) (Real.log (330837 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (330837 / 200000) = -Real.log (200000 / 330837) := by
    rw [show ((330837 / 200000) : ℝ) = ((200000 / 330837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16591427 / 15625000) ≤ -Real.log (69163 / 200000) ∧
    -Real.log (69163 / 200000) ≤ (106185133 / 100000000) := by
  have h := checkLog_sound (w := (30837 / 169163)) (n := 12)
    (lo := (92176037 / 250000000)) (hi := (368704149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69163) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69163) = 1/(69163 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106185133 / 100000000) (-16591427 / 15625000) (Real.log (69163 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (504631479 / 1000000000) ≤ -Real.log (8000 / 13251) ∧
    -Real.log (8000 / 13251) ≤ (12615787 / 25000000) := by
  have h := checkLog_sound (w := (5251 / 21251)) (n := 12)
    (lo := (504631479 / 1000000000)) (hi := (12615787 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13251 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13251 / 8000) = 1/(8000 / 13251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (504631479 / 1000000000) (12615787 / 25000000) (Real.log (13251 / 8000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (13251 / 8000) = -Real.log (8000 / 13251) := by
    rw [show ((13251 / 8000) : ℝ) = ((8000 / 13251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1068204331 / 1000000000) ≤ -Real.log (2749 / 8000) ∧
    -Real.log (2749 / 8000) ≤ (1068204333 / 1000000000) := by
  have h := checkLog_sound (w := (1251 / 6749)) (n := 12)
    (lo := (375057151 / 1000000000)) (hi := (1465067 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2749) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4000 / 2749) = 1/(2749 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1068204333 / 1000000000) (-1068204331 / 1000000000) (Real.log (2749 / 8000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1034174027 / 500000000) ≤ -Real.log (50000000000 / 395587127879) ∧
    -Real.log (50000000000 / 395587127879) ≤ (2068348057 / 1000000000) := by
  have h := checkLog_sound (w := (195587127879 / 595587127879)) (n := 12)
    (lo := (341026847 / 500000000)) (hi := (136410739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395587127879 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(395587127879 / 200000000000) = 1/(50000000000 / 395587127879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1034174027 / 500000000) (2068348057 / 1000000000) (Real.log (395587127879 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (395587127879 / 50000000000) = -Real.log (50000000000 / 395587127879) := by
    rw [show ((395587127879 / 50000000000) : ℝ) = ((50000000000 / 395587127879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (519600053 / 250000000) ≤ -Real.log (500000000000 / 3995836855073) ∧
    -Real.log (500000000000 / 3995836855073) ≤ (415680043 / 200000000) := by
  have h := checkLog_sound (w := (1995836855073 / 5995836855073)) (n := 12)
    (lo := (173026463 / 250000000)) (hi := (692105853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3995836855073 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3995836855073 / 2000000000000) = 1/(500000000000 / 3995836855073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (519600053 / 250000000) (415680043 / 200000000) (Real.log (3995836855073 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3995836855073 / 500000000000) = -Real.log (500000000000 / 3995836855073) := by
    rw [show ((3995836855073 / 500000000000) : ℝ) = ((500000000000 / 3995836855073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (195644971 / 125000000) ≤ -Real.log (125000000000 / 597929890259) ∧
    -Real.log (125000000000 / 597929890259) ≤ (1565159771 / 1000000000) := by
  have h := checkLog_sound (w := (97929890259 / 1097929890259)) (n := 12)
    (lo := (698693 / 3906250)) (hi := (178865409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597929890259 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(597929890259 / 500000000000) = 1/(125000000000 / 597929890259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (195644971 / 125000000) (1565159771 / 1000000000) (Real.log (597929890259 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (597929890259 / 125000000000) = -Real.log (125000000000 / 597929890259) := by
    rw [show ((597929890259 / 125000000000) : ℝ) = ((125000000000 / 597929890259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (157283581 / 100000000) ≤ -Real.log (62500000000 / 301268643143) ∧
    -Real.log (62500000000 / 301268643143) ≤ (1572835813 / 1000000000) := by
  have h := checkLog_sound (w := (51268643143 / 551268643143)) (n := 12)
    (lo := (3730829 / 20000000)) (hi := (186541451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301268643143 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(301268643143 / 250000000000) = 1/(62500000000 / 301268643143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (157283581 / 100000000) (1572835813 / 1000000000) (Real.log (301268643143 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (301268643143 / 62500000000) = -Real.log (62500000000 / 301268643143) := by
    rw [show ((301268643143 / 62500000000) : ℝ) = ((62500000000 / 301268643143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0011

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0012Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0012
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

theorem reflection_log_1_neg : (12646361 / 31250000) ≤ -Real.log (2560 / 3837) ∧
    -Real.log (2560 / 3837) ≤ (404683553 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 6397)) (n := 12)
    (lo := (12646361 / 31250000)) (hi := (404683553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3837 / 2560) = 1/(2560 / 3837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12646361 / 31250000) (404683553 / 1000000000) (Real.log (3837 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3837 / 2560) = -Real.log (2560 / 3837) := by
    rw [show ((3837 / 2560) : ℝ) = ((2560 / 3837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (172701543 / 250000000) ≤ -Real.log (1283 / 2560) ∧
    -Real.log (1283 / 2560) ≤ (690806173 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3843)) (n := 12)
    (lo := (172701543 / 250000000)) (hi := (690806173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1283) = 1/(1283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-690806173 / 1000000000) (-172701543 / 250000000) (Real.log (1283 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201950693 / 500000000) ≤ -Real.log (1280 / 1917) ∧
    -Real.log (1280 / 1917) ≤ (403901387 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 3197)) (n := 12)
    (lo := (201950693 / 500000000)) (hi := (403901387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917 / 1280) = 1/(1280 / 1917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201950693 / 500000000) (403901387 / 1000000000) (Real.log (1917 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1917 / 1280) = -Real.log (1280 / 1917) := by
    rw [show ((1917 / 1280) : ℝ) = ((1280 / 1917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86058829 / 125000000) ≤ -Real.log (643 / 1280) ∧
    -Real.log (643 / 1280) ≤ (688470633 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 1923)) (n := 12)
    (lo := (86058829 / 125000000)) (hi := (688470633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 643) = 1/(643 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-688470633 / 1000000000) (-86058829 / 125000000) (Real.log (643 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (345987309 / 500000000) ≤ -Real.log (1280 / 2557) ∧
    -Real.log (1280 / 2557) ≤ (691974619 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3837)) (n := 12)
    (lo := (345987309 / 500000000)) (hi := (691974619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2557 / 1280) = 1/(1280 / 2557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (345987309 / 500000000) (691974619 / 1000000000) (Real.log (2557 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2557 / 1280) = -Real.log (1280 / 2557) := by
    rw [show ((2557 / 1280) : ℝ) = ((1280 / 2557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6056003063 / 1000000000) ≤ -Real.log (3 / 1280) ∧
    -Real.log (3 / 1280) ≤ (11828131 / 1953125) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(5 / 3) = 1/(3 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11828131 / 1953125) (-6056003063 / 1000000000) (Real.log (3 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (690800679 / 1000000000) ≤ -Real.log (640 / 1277) ∧
    -Real.log (640 / 1277) ≤ (17270017 / 25000000) := by
  have h := checkLog_sound (w := (637 / 1917)) (n := 12)
    (lo := (690800679 / 1000000000)) (hi := (17270017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277 / 640) = 1/(640 / 1277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (690800679 / 1000000000) (17270017 / 25000000) (Real.log (1277 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1277 / 640) = -Real.log (640 / 1277) := by
    rw [show ((1277 / 640) : ℝ) = ((640 / 1277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5362855883 / 1000000000) ≤ -Real.log (3 / 640) ∧
    -Real.log (3 / 640) ≤ (5362855891 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(5 / 3) = 1/(3 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5362855891 / 1000000000) (-5362855883 / 1000000000) (Real.log (3 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (114416917 / 200000000) ≤ -Real.log (1000000 / 1771957) ∧
    -Real.log (1000000 / 1771957) ≤ (286042293 / 500000000) := by
  have h := checkLog_sound (w := (771957 / 2771957)) (n := 12)
    (lo := (114416917 / 200000000)) (hi := (286042293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1771957 / 1000000) = 1/(1000000 / 1771957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (114416917 / 200000000) (286042293 / 500000000) (Real.log (1771957 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1771957 / 1000000) = -Real.log (1000000 / 1771957) := by
    rw [show ((1771957 / 1000000) : ℝ) = ((1000000 / 1771957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (147822107 / 100000000) ≤ -Real.log (228043 / 1000000) ∧
    -Real.log (228043 / 1000000) ≤ (1478221073 / 1000000000) := by
  have h := checkLog_sound (w := (21957 / 478043)) (n := 12)
    (lo := (9192671 / 100000000)) (hi := (91926711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228043) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 228043) = 1/(228043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1478221073 / 1000000000) (-147822107 / 100000000) (Real.log (228043 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (574126003 / 1000000000) ≤ -Real.log (500000 / 887789) ∧
    -Real.log (500000 / 887789) ≤ (143531501 / 250000000) := by
  have h := checkLog_sound (w := (387789 / 1387789)) (n := 12)
    (lo := (574126003 / 1000000000)) (hi := (143531501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887789 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887789 / 500000) = 1/(500000 / 887789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (574126003 / 1000000000) (143531501 / 250000000) (Real.log (887789 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (887789 / 500000) = -Real.log (500000 / 887789) := by
    rw [show ((887789 / 500000) : ℝ) = ((500000 / 887789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1494227069 / 1000000000) ≤ -Real.log (112211 / 500000) ∧
    -Real.log (112211 / 500000) ≤ (11673649 / 7812500) := by
  have h := checkLog_sound (w := (12789 / 237211)) (n := 12)
    (lo := (107932709 / 1000000000)) (hi := (10793271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112211) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 112211) = 1/(112211 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11673649 / 7812500) (-1494227069 / 1000000000) (Real.log (112211 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (250440671 / 500000000) ≤ -Real.log (40000 / 66007) ∧
    -Real.log (40000 / 66007) ≤ (500881343 / 1000000000) := by
  have h := checkLog_sound (w := (26007 / 106007)) (n := 12)
    (lo := (250440671 / 500000000)) (hi := (500881343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66007 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66007 / 40000) = 1/(40000 / 66007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (250440671 / 500000000) (500881343 / 1000000000) (Real.log (66007 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (66007 / 40000) = -Real.log (40000 / 66007) := by
    rw [show ((66007 / 40000) : ℝ) = ((40000 / 66007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (131290281 / 125000000) ≤ -Real.log (13993 / 40000) ∧
    -Real.log (13993 / 40000) ≤ (4201289 / 4000000) := by
  have h := checkLog_sound (w := (6007 / 33993)) (n := 12)
    (lo := (89293767 / 250000000)) (hi := (357175069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13993) = 1/(13993 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4201289 / 4000000) (-131290281 / 125000000) (Real.log (13993 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125827261 / 250000000) ≤ -Real.log (500000 / 827093) ∧
    -Real.log (500000 / 827093) ≤ (100661809 / 200000000) := by
  have h := checkLog_sound (w := (327093 / 1327093)) (n := 12)
    (lo := (125827261 / 250000000)) (hi := (100661809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827093 / 500000) = 1/(500000 / 827093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125827261 / 250000000) (100661809 / 200000000) (Real.log (827093 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (827093 / 500000) = -Real.log (500000 / 827093) := by
    rw [show ((827093 / 500000) : ℝ) = ((500000 / 827093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53092711 / 50000000) ≤ -Real.log (172907 / 500000) ∧
    -Real.log (172907 / 500000) ≤ (530927111 / 500000000) := by
  have h := checkLog_sound (w := (77093 / 422907)) (n := 12)
    (lo := (2304419 / 6250000)) (hi := (368707041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 172907) = 1/(172907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-530927111 / 500000000) (-53092711 / 50000000) (Real.log (172907 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (410061131 / 200000000) ≤ -Real.log (25000000000 / 194256894533) ∧
    -Real.log (25000000000 / 194256894533) ≤ (1025152829 / 500000000) := by
  have h := checkLog_sound (w := (94256894533 / 294256894533)) (n := 12)
    (lo := (132802259 / 200000000)) (hi := (20750353 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194256894533 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(194256894533 / 100000000000) = 1/(25000000000 / 194256894533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (410061131 / 200000000) (1025152829 / 500000000) (Real.log (194256894533 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (194256894533 / 25000000000) = -Real.log (25000000000 / 194256894533) := by
    rw [show ((194256894533 / 25000000000) : ℝ) = ((25000000000 / 194256894533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2068353073 / 1000000000) ≤ -Real.log (125000000000 / 988972783417) ∧
    -Real.log (125000000000 / 988972783417) ≤ (517088269 / 250000000) := by
  have h := checkLog_sound (w := (488972783417 / 1488972783417)) (n := 12)
    (lo := (682058713 / 1000000000)) (hi := (341029357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988972783417 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(988972783417 / 500000000000) = 1/(125000000000 / 988972783417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2068353073 / 1000000000) (517088269 / 250000000) (Real.log (988972783417 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (988972783417 / 125000000000) = -Real.log (125000000000 / 988972783417) := by
    rw [show ((988972783417 / 125000000000) : ℝ) = ((125000000000 / 988972783417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1551203591 / 1000000000) ≤ -Real.log (250000000000 / 1179286071607) ∧
    -Real.log (250000000000 / 1179286071607) ≤ (775601797 / 500000000) := by
  have h := checkLog_sound (w := (179286071607 / 2179286071607)) (n := 12)
    (lo := (164909231 / 1000000000)) (hi := (10306827 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179286071607 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1179286071607 / 1000000000000) = 1/(250000000000 / 1179286071607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1551203591 / 1000000000) (775601797 / 500000000) (Real.log (1179286071607 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1179286071607 / 250000000000) = -Real.log (250000000000 / 1179286071607) := by
    rw [show ((1179286071607 / 250000000000) : ℝ) = ((250000000000 / 1179286071607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (6113919 / 3906250) ≤ -Real.log (15625000000 / 74741497597) ∧
    -Real.log (15625000000 / 74741497597) ≤ (1565163267 / 1000000000) := by
  have h := checkLog_sound (w := (12241497597 / 137241497597)) (n := 12)
    (lo := (22358613 / 125000000)) (hi := (35773781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74741497597 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(74741497597 / 62500000000) = 1/(15625000000 / 74741497597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (6113919 / 3906250) (1565163267 / 1000000000) (Real.log (74741497597 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (74741497597 / 15625000000) = -Real.log (15625000000 / 74741497597) := by
    rw [show ((74741497597 / 15625000000) : ℝ) = ((15625000000 / 74741497597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0012

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0013Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0013
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

theorem reflection_log_1_neg : (201950693 / 500000000) ≤ -Real.log (1280 / 1917) ∧
    -Real.log (1280 / 1917) ≤ (403901387 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 3197)) (n := 12)
    (lo := (201950693 / 500000000)) (hi := (403901387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917 / 1280) = 1/(1280 / 1917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (201950693 / 500000000) (403901387 / 1000000000) (Real.log (1917 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1917 / 1280) = -Real.log (1280 / 1917) := by
    rw [show ((1917 / 1280) : ℝ) = ((1280 / 1917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86058829 / 125000000) ≤ -Real.log (643 / 1280) ∧
    -Real.log (643 / 1280) ≤ (688470633 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 1923)) (n := 12)
    (lo := (86058829 / 125000000)) (hi := (688470633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 643) = 1/(643 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-688470633 / 1000000000) (-86058829 / 125000000) (Real.log (643 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (403118607 / 1000000000) ≤ -Real.log (2560 / 3831) ∧
    -Real.log (2560 / 3831) ≤ (25194913 / 62500000) := by
  have h := checkLog_sound (w := (1271 / 6391)) (n := 12)
    (lo := (403118607 / 1000000000)) (hi := (25194913 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3831 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3831 / 2560) = 1/(2560 / 3831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (403118607 / 1000000000) (25194913 / 62500000) (Real.log (3831 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3831 / 2560) = -Real.log (2560 / 3831) := by
    rw [show ((3831 / 2560) : ℝ) = ((2560 / 3831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (343070267 / 500000000) ≤ -Real.log (1289 / 2560) ∧
    -Real.log (1289 / 2560) ≤ (137228107 / 200000000) := by
  have h := checkLog_sound (w := (1271 / 3849)) (n := 12)
    (lo := (343070267 / 500000000)) (hi := (137228107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1289) = 1/(1289 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-137228107 / 200000000) (-343070267 / 500000000) (Real.log (1289 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (690800679 / 1000000000) ≤ -Real.log (640 / 1277) ∧
    -Real.log (640 / 1277) ≤ (17270017 / 25000000) := by
  have h := checkLog_sound (w := (637 / 1917)) (n := 12)
    (lo := (690800679 / 1000000000)) (hi := (17270017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277 / 640) = 1/(640 / 1277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (690800679 / 1000000000) (17270017 / 25000000) (Real.log (1277 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1277 / 640) = -Real.log (640 / 1277) := by
    rw [show ((1277 / 640) : ℝ) = ((640 / 1277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5362855883 / 1000000000) ≤ -Real.log (3 / 640) ∧
    -Real.log (3 / 640) ≤ (5362855891 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(5 / 3) = 1/(3 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5362855891 / 1000000000) (-5362855883 / 1000000000) (Real.log (3 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (689625361 / 1000000000) ≤ -Real.log (1280 / 2551) ∧
    -Real.log (1280 / 2551) ≤ (344812681 / 500000000) := by
  have h := checkLog_sound (w := (1271 / 3831)) (n := 12)
    (lo := (689625361 / 1000000000)) (hi := (344812681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2551 / 1280) = 1/(1280 / 2551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (689625361 / 1000000000) (344812681 / 500000000) (Real.log (2551 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2551 / 1280) = -Real.log (1280 / 2551) := by
    rw [show ((2551 / 1280) : ℝ) = ((1280 / 2551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (198295631 / 40000000) ≤ -Real.log (9 / 1280) ∧
    -Real.log (9 / 1280) ≤ (4957390783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(10 / 9) = 1/(9 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4957390783 / 1000000000) (-198295631 / 40000000) (Real.log (9 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142548199 / 250000000) ≤ -Real.log (31250 / 55269) ∧
    -Real.log (31250 / 55269) ≤ (570192797 / 1000000000) := by
  have h := checkLog_sound (w := (24019 / 86519)) (n := 12)
    (lo := (142548199 / 250000000)) (hi := (570192797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55269 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55269 / 31250) = 1/(31250 / 55269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142548199 / 250000000) (570192797 / 1000000000) (Real.log (55269 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (55269 / 31250) = -Real.log (31250 / 55269) := by
    rw [show ((55269 / 31250) : ℝ) = ((31250 / 55269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (292728407 / 200000000) ≤ -Real.log (7231 / 31250) ∧
    -Real.log (7231 / 31250) ≤ (731821019 / 500000000) := by
  have h := checkLog_sound (w := (1163 / 30087)) (n := 12)
    (lo := (3093907 / 40000000)) (hi := (19336919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14462) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 14462) = 1/(7231 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-731821019 / 500000000) (-292728407 / 200000000) (Real.log (7231 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (572085149 / 1000000000) ≤ -Real.log (500000 / 885979) ∧
    -Real.log (500000 / 885979) ≤ (11441703 / 20000000) := by
  have h := checkLog_sound (w := (385979 / 1385979)) (n := 12)
    (lo := (572085149 / 1000000000)) (hi := (11441703 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885979 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885979 / 500000) = 1/(500000 / 885979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (572085149 / 1000000000) (11441703 / 20000000) (Real.log (885979 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (885979 / 500000) = -Real.log (500000 / 885979) := by
    rw [show ((885979 / 500000) : ℝ) = ((500000 / 885979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (295645091 / 200000000) ≤ -Real.log (114021 / 500000) ∧
    -Real.log (114021 / 500000) ≤ (739112729 / 500000000) := by
  have h := checkLog_sound (w := (10979 / 239021)) (n := 12)
    (lo := (18386219 / 200000000)) (hi := (11491387 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114021) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 114021) = 1/(114021 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-739112729 / 500000000) (-295645091 / 200000000) (Real.log (114021 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49861781 / 100000000) ≤ -Real.log (250000 / 411611) ∧
    -Real.log (250000 / 411611) ≤ (498617811 / 1000000000) := by
  have h := checkLog_sound (w := (161611 / 661611)) (n := 12)
    (lo := (49861781 / 100000000)) (hi := (498617811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411611 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411611 / 250000) = 1/(250000 / 411611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49861781 / 100000000) (498617811 / 1000000000) (Real.log (411611 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (411611 / 250000) = -Real.log (250000 / 411611) := by
    rw [show ((411611 / 250000) : ℝ) = ((250000 / 411611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1039713389 / 1000000000) ≤ -Real.log (88389 / 250000) ∧
    -Real.log (88389 / 250000) ≤ (1039713391 / 1000000000) := by
  have h := checkLog_sound (w := (36611 / 213389)) (n := 12)
    (lo := (346566209 / 1000000000)) (hi := (34656621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88389) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 88389) = 1/(88389 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1039713391 / 1000000000) (-1039713389 / 1000000000) (Real.log (88389 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125220487 / 250000000) ≤ -Real.log (15625 / 25784) ∧
    -Real.log (15625 / 25784) ≤ (500881949 / 1000000000) := by
  have h := checkLog_sound (w := (10159 / 41409)) (n := 12)
    (lo := (125220487 / 250000000)) (hi := (500881949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25784 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25784 / 15625) = 1/(15625 / 25784) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125220487 / 250000000) (500881949 / 1000000000) (Real.log (25784 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25784 / 15625) = -Real.log (15625 / 25784) := by
    rw [show ((25784 / 15625) : ℝ) = ((15625 / 25784) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1050325107 / 1000000000) ≤ -Real.log (5466 / 15625) ∧
    -Real.log (5466 / 15625) ≤ (1050325109 / 1000000000) := by
  have h := checkLog_sound (w := (4693 / 26557)) (n := 12)
    (lo := (357177927 / 1000000000)) (hi := (44647241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10932) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 10932) = 1/(5466 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1050325109 / 1000000000) (-1050325107 / 1000000000) (Real.log (5466 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (127114677 / 62500000) ≤ -Real.log (500000000000 / 3821670584981) ∧
    -Real.log (500000000000 / 3821670584981) ≤ (406766967 / 200000000) := by
  have h := checkLog_sound (w := (1821670584981 / 5821670584981)) (n := 12)
    (lo := (80942559 / 125000000)) (hi := (647540473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821670584981 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3821670584981 / 2000000000000) = 1/(500000000000 / 3821670584981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127114677 / 62500000) (406766967 / 200000000) (Real.log (3821670584981 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3821670584981 / 500000000000) = -Real.log (500000000000 / 3821670584981) := by
    rw [show ((3821670584981 / 500000000000) : ℝ) = ((500000000000 / 3821670584981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (410062121 / 200000000) ≤ -Real.log (25000000000 / 194257856009) ∧
    -Real.log (25000000000 / 194257856009) ≤ (128144413 / 62500000) := by
  have h := checkLog_sound (w := (94257856009 / 294257856009)) (n := 12)
    (lo := (132803249 / 200000000)) (hi := (332008123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194257856009 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(194257856009 / 100000000000) = 1/(25000000000 / 194257856009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (410062121 / 200000000) (128144413 / 62500000) (Real.log (194257856009 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (194257856009 / 25000000000) = -Real.log (25000000000 / 194257856009) := by
    rw [show ((194257856009 / 25000000000) : ℝ) = ((25000000000 / 194257856009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1538331199 / 1000000000) ≤ -Real.log (250000000000 / 1164203124823) ∧
    -Real.log (250000000000 / 1164203124823) ≤ (769165601 / 500000000) := by
  have h := checkLog_sound (w := (164203124823 / 2164203124823)) (n := 12)
    (lo := (152036839 / 1000000000)) (hi := (3800921 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164203124823 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1164203124823 / 1000000000000) = 1/(250000000000 / 1164203124823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1538331199 / 1000000000) (769165601 / 500000000) (Real.log (1164203124823 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1164203124823 / 250000000000) = -Real.log (250000000000 / 1164203124823) := by
    rw [show ((1164203124823 / 250000000000) : ℝ) = ((250000000000 / 1164203124823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (310241411 / 200000000) ≤ -Real.log (500000000000 / 2358580314673) ∧
    -Real.log (500000000000 / 2358580314673) ≤ (775603529 / 500000000) := by
  have h := checkLog_sound (w := (358580314673 / 4358580314673)) (n := 12)
    (lo := (32982539 / 200000000)) (hi := (20614087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2358580314673 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2358580314673 / 2000000000000) = 1/(500000000000 / 2358580314673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (310241411 / 200000000) (775603529 / 500000000) (Real.log (2358580314673 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2358580314673 / 500000000000) = -Real.log (500000000000 / 2358580314673) := by
    rw [show ((2358580314673 / 500000000000) : ℝ) = ((500000000000 / 2358580314673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0013

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0014Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0014
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

theorem reflection_log_1_neg : (403118607 / 1000000000) ≤ -Real.log (2560 / 3831) ∧
    -Real.log (2560 / 3831) ≤ (25194913 / 62500000) := by
  have h := checkLog_sound (w := (1271 / 6391)) (n := 12)
    (lo := (403118607 / 1000000000)) (hi := (25194913 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3831 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3831 / 2560) = 1/(2560 / 3831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (403118607 / 1000000000) (25194913 / 62500000) (Real.log (3831 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3831 / 2560) = -Real.log (2560 / 3831) := by
    rw [show ((3831 / 2560) : ℝ) = ((2560 / 3831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (343070267 / 500000000) ≤ -Real.log (1289 / 2560) ∧
    -Real.log (1289 / 2560) ≤ (137228107 / 200000000) := by
  have h := checkLog_sound (w := (1271 / 3849)) (n := 12)
    (lo := (343070267 / 500000000)) (hi := (137228107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1289) = 1/(1289 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-137228107 / 200000000) (-343070267 / 500000000) (Real.log (1289 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80467043 / 200000000) ≤ -Real.log (640 / 957) ∧
    -Real.log (640 / 957) ≤ (25145951 / 62500000) := by
  have h := checkLog_sound (w := (317 / 1597)) (n := 12)
    (lo := (80467043 / 200000000)) (hi := (25145951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957 / 640) = 1/(640 / 957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (80467043 / 200000000) (25145951 / 62500000) (Real.log (957 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (957 / 640) = -Real.log (640 / 957) := by
    rw [show ((957 / 640) : ℝ) = ((640 / 957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (683815853 / 1000000000) ≤ -Real.log (323 / 640) ∧
    -Real.log (323 / 640) ≤ (341907927 / 500000000) := by
  have h := checkLog_sound (w := (317 / 963)) (n := 12)
    (lo := (683815853 / 1000000000)) (hi := (341907927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 323) = 1/(323 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-341907927 / 500000000) (-683815853 / 1000000000) (Real.log (323 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (689625361 / 1000000000) ≤ -Real.log (1280 / 2551) ∧
    -Real.log (1280 / 2551) ≤ (344812681 / 500000000) := by
  have h := checkLog_sound (w := (1271 / 3831)) (n := 12)
    (lo := (689625361 / 1000000000)) (hi := (344812681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2551 / 1280) = 1/(1280 / 2551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (689625361 / 1000000000) (344812681 / 500000000) (Real.log (2551 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2551 / 1280) = -Real.log (1280 / 2551) := by
    rw [show ((2551 / 1280) : ℝ) = ((1280 / 2551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (198295631 / 40000000) ≤ -Real.log (9 / 1280) ∧
    -Real.log (9 / 1280) ≤ (4957390783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(10 / 9) = 1/(9 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4957390783 / 1000000000) (-198295631 / 40000000) (Real.log (9 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (688448659 / 1000000000) ≤ -Real.log (320 / 637) ∧
    -Real.log (320 / 637) ≤ (34422433 / 50000000) := by
  have h := checkLog_sound (w := (317 / 957)) (n := 12)
    (lo := (688448659 / 1000000000)) (hi := (34422433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637 / 320) = 1/(320 / 637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (688448659 / 1000000000) (34422433 / 50000000) (Real.log (637 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (637 / 320) = -Real.log (320 / 637) := by
    rw [show ((637 / 320) : ℝ) = ((320 / 637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4669708703 / 1000000000) ≤ -Real.log (3 / 320) ∧
    -Real.log (3 / 320) ≤ (466970871 / 100000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5 / 3) = 1/(3 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-466970871 / 100000000) (-4669708703 / 1000000000) (Real.log (3 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (14209843 / 25000000) ≤ -Real.log (1000000 / 1765429) ∧
    -Real.log (1000000 / 1765429) ≤ (568393721 / 1000000000) := by
  have h := checkLog_sound (w := (765429 / 2765429)) (n := 12)
    (lo := (14209843 / 25000000)) (hi := (568393721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1765429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1765429 / 1000000) = 1/(1000000 / 1765429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (14209843 / 25000000) (568393721 / 1000000000) (Real.log (1765429 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1765429 / 1000000) = -Real.log (1000000 / 1765429) := by
    rw [show ((1765429 / 1000000) : ℝ) = ((1000000 / 1765429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1449996963 / 1000000000) ≤ -Real.log (234571 / 1000000) ∧
    -Real.log (234571 / 1000000) ≤ (724998483 / 500000000) := by
  have h := checkLog_sound (w := (15429 / 484571)) (n := 12)
    (lo := (63702603 / 1000000000)) (hi := (15925651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 234571) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 234571) = 1/(234571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-724998483 / 500000000) (-1449996963 / 1000000000) (Real.log (234571 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (570193361 / 1000000000) ≤ -Real.log (1000000 / 1768609) ∧
    -Real.log (1000000 / 1768609) ≤ (285096681 / 500000000) := by
  have h := checkLog_sound (w := (768609 / 2768609)) (n := 12)
    (lo := (570193361 / 1000000000)) (hi := (285096681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1768609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1768609 / 1000000) = 1/(1000000 / 1768609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (570193361 / 1000000000) (285096681 / 500000000) (Real.log (1768609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1768609 / 1000000) = -Real.log (1000000 / 1768609) := by
    rw [show ((1768609 / 1000000) : ℝ) = ((1000000 / 1768609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1463646357 / 1000000000) ≤ -Real.log (231391 / 1000000) ∧
    -Real.log (231391 / 1000000) ≤ (36591159 / 25000000) := by
  have h := checkLog_sound (w := (18609 / 481391)) (n := 12)
    (lo := (77351997 / 1000000000)) (hi := (38675999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231391) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 231391) = 1/(231391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36591159 / 25000000) (-1463646357 / 1000000000) (Real.log (231391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (248230573 / 500000000) ≤ -Real.log (1000000 / 1642897) ∧
    -Real.log (1000000 / 1642897) ≤ (496461147 / 1000000000) := by
  have h := checkLog_sound (w := (642897 / 2642897)) (n := 12)
    (lo := (248230573 / 500000000)) (hi := (496461147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642897 / 1000000) = 1/(1000000 / 1642897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (248230573 / 500000000) (496461147 / 1000000000) (Real.log (1642897 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1642897 / 1000000) = -Real.log (1000000 / 1642897) := by
    rw [show ((1642897 / 1000000) : ℝ) = ((1000000 / 1642897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (514865511 / 500000000) ≤ -Real.log (357103 / 1000000) ∧
    -Real.log (357103 / 1000000) ≤ (64358189 / 62500000) := by
  have h := checkLog_sound (w := (142897 / 857103)) (n := 12)
    (lo := (168291921 / 500000000)) (hi := (336583843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357103) = 1/(357103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-64358189 / 62500000) (-514865511 / 500000000) (Real.log (357103 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (249309209 / 500000000) ≤ -Real.log (200000 / 329289) ∧
    -Real.log (200000 / 329289) ≤ (498618419 / 1000000000) := by
  have h := checkLog_sound (w := (129289 / 529289)) (n := 12)
    (lo := (249309209 / 500000000)) (hi := (498618419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329289 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329289 / 200000) = 1/(200000 / 329289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (249309209 / 500000000) (498618419 / 1000000000) (Real.log (329289 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (329289 / 200000) = -Real.log (200000 / 329289) := by
    rw [show ((329289 / 200000) : ℝ) = ((200000 / 329289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (519858109 / 500000000) ≤ -Real.log (70711 / 200000) ∧
    -Real.log (70711 / 200000) ≤ (51985811 / 50000000) := by
  have h := checkLog_sound (w := (29289 / 170711)) (n := 12)
    (lo := (173284519 / 500000000)) (hi := (346569039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70711) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 70711) = 1/(70711 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-51985811 / 50000000) (-519858109 / 500000000) (Real.log (70711 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (504597671 / 250000000) ≤ -Real.log (500000000000 / 3763101576921) ∧
    -Real.log (500000000000 / 3763101576921) ≤ (2018390687 / 1000000000) := by
  have h := checkLog_sound (w := (1763101576921 / 5763101576921)) (n := 12)
    (lo := (158024081 / 250000000)) (hi := (25283853 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3763101576921 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3763101576921 / 2000000000000) = 1/(500000000000 / 3763101576921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (504597671 / 250000000) (2018390687 / 1000000000) (Real.log (3763101576921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3763101576921 / 500000000000) = -Real.log (500000000000 / 3763101576921) := by
    rw [show ((3763101576921 / 500000000000) : ℝ) = ((500000000000 / 3763101576921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2033839719 / 1000000000) ≤ -Real.log (500000000000 / 3821689261899) ∧
    -Real.log (500000000000 / 3821689261899) ≤ (1016919861 / 500000000) := by
  have h := checkLog_sound (w := (1821689261899 / 5821689261899)) (n := 12)
    (lo := (647545359 / 1000000000)) (hi := (8094317 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821689261899 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3821689261899 / 2000000000000) = 1/(500000000000 / 3821689261899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2033839719 / 1000000000) (1016919861 / 500000000) (Real.log (3821689261899 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3821689261899 / 500000000000) = -Real.log (500000000000 / 3821689261899) := by
    rw [show ((3821689261899 / 500000000000) : ℝ) = ((500000000000 / 3821689261899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1526192169 / 1000000000) ≤ -Real.log (125000000000 / 575078128719) ∧
    -Real.log (125000000000 / 575078128719) ≤ (381548043 / 250000000) := by
  have h := checkLog_sound (w := (75078128719 / 1075078128719)) (n := 12)
    (lo := (139897809 / 1000000000)) (hi := (13989781 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575078128719 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(575078128719 / 500000000000) = 1/(125000000000 / 575078128719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1526192169 / 1000000000) (381548043 / 250000000) (Real.log (575078128719 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (575078128719 / 125000000000) = -Real.log (125000000000 / 575078128719) := by
    rw [show ((575078128719 / 125000000000) : ℝ) = ((125000000000 / 575078128719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (307666927 / 200000000) ≤ -Real.log (500000000000 / 2328414249551) ∧
    -Real.log (500000000000 / 2328414249551) ≤ (769167319 / 500000000) := by
  have h := checkLog_sound (w := (328414249551 / 4328414249551)) (n := 12)
    (lo := (6081611 / 40000000)) (hi := (38010069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2328414249551 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2328414249551 / 2000000000000) = 1/(500000000000 / 2328414249551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (307666927 / 200000000) (769167319 / 500000000) (Real.log (2328414249551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2328414249551 / 500000000000) = -Real.log (500000000000 / 2328414249551) := by
    rw [show ((2328414249551 / 500000000000) : ℝ) = ((500000000000 / 2328414249551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0014

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0015Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0015
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

theorem reflection_log_1_neg : (80467043 / 200000000) ≤ -Real.log (640 / 957) ∧
    -Real.log (640 / 957) ≤ (25145951 / 62500000) := by
  have h := checkLog_sound (w := (317 / 1597)) (n := 12)
    (lo := (80467043 / 200000000)) (hi := (25145951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957 / 640) = 1/(640 / 957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80467043 / 200000000) (25145951 / 62500000) (Real.log (957 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (957 / 640) = -Real.log (640 / 957) := by
    rw [show ((957 / 640) : ℝ) = ((640 / 957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (683815853 / 1000000000) ≤ -Real.log (323 / 640) ∧
    -Real.log (323 / 640) ≤ (341907927 / 500000000) := by
  have h := checkLog_sound (w := (317 / 963)) (n := 12)
    (lo := (683815853 / 1000000000)) (hi := (341907927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 323) = 1/(323 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-341907927 / 500000000) (-683815853 / 1000000000) (Real.log (323 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50193901 / 125000000) ≤ -Real.log (512 / 765) ∧
    -Real.log (512 / 765) ≤ (401551209 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 1277)) (n := 12)
    (lo := (50193901 / 125000000)) (hi := (401551209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765 / 512) = 1/(512 / 765) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50193901 / 125000000) (401551209 / 1000000000) (Real.log (765 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (765 / 512) = -Real.log (512 / 765) := by
    rw [show ((765 / 512) : ℝ) = ((512 / 765) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (681496563 / 1000000000) ≤ -Real.log (259 / 512) ∧
    -Real.log (259 / 512) ≤ (170374141 / 250000000) := by
  have h := checkLog_sound (w := (253 / 771)) (n := 12)
    (lo := (681496563 / 1000000000)) (hi := (170374141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 259) = 1/(259 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170374141 / 250000000) (-681496563 / 1000000000) (Real.log (259 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (688448659 / 1000000000) ≤ -Real.log (320 / 637) ∧
    -Real.log (320 / 637) ≤ (34422433 / 50000000) := by
  have h := checkLog_sound (w := (317 / 957)) (n := 12)
    (lo := (688448659 / 1000000000)) (hi := (34422433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637 / 320) = 1/(320 / 637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (688448659 / 1000000000) (34422433 / 50000000) (Real.log (637 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (637 / 320) = -Real.log (320 / 637) := by
    rw [show ((637 / 320) : ℝ) = ((320 / 637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (4669708703 / 1000000000) ≤ -Real.log (3 / 320) ∧
    -Real.log (3 / 320) ≤ (466970871 / 100000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5 / 3) = 1/(3 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-466970871 / 100000000) (-4669708703 / 1000000000) (Real.log (3 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171817643 / 250000000) ≤ -Real.log (256 / 509) ∧
    -Real.log (256 / 509) ≤ (687270573 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 765)) (n := 12)
    (lo := (171817643 / 250000000)) (hi := (687270573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(509 / 256) = 1/(256 / 509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171817643 / 250000000) (687270573 / 1000000000) (Real.log (509 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (509 / 256) = -Real.log (256 / 509) := by
    rw [show ((509 / 256) : ℝ) = ((256 / 509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (138955161 / 31250000) ≤ -Real.log (3 / 256) ∧
    -Real.log (3 / 256) ≤ (4446565159 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4 / 3) = 1/(3 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4446565159 / 1000000000) (-138955161 / 31250000) (Real.log (3 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (566661763 / 1000000000) ≤ -Real.log (500000 / 881187) ∧
    -Real.log (500000 / 881187) ≤ (141665441 / 250000000) := by
  have h := checkLog_sound (w := (381187 / 1381187)) (n := 12)
    (lo := (566661763 / 1000000000)) (hi := (141665441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881187 / 500000) = 1/(500000 / 881187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (566661763 / 1000000000) (141665441 / 250000000) (Real.log (881187 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (881187 / 500000) = -Real.log (500000 / 881187) := by
    rw [show ((881187 / 500000) : ℝ) = ((500000 / 881187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (359264317 / 250000000) ≤ -Real.log (118813 / 500000) ∧
    -Real.log (118813 / 500000) ≤ (1437057271 / 1000000000) := by
  have h := checkLog_sound (w := (6187 / 243813)) (n := 12)
    (lo := (12690727 / 250000000)) (hi := (50762909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 118813) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 118813) = 1/(118813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1437057271 / 1000000000) (-359264317 / 250000000) (Real.log (118813 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (284197143 / 500000000) ≤ -Real.log (100000 / 176543) ∧
    -Real.log (100000 / 176543) ≤ (568394287 / 1000000000) := by
  have h := checkLog_sound (w := (76543 / 276543)) (n := 12)
    (lo := (284197143 / 500000000)) (hi := (568394287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176543 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176543 / 100000) = 1/(100000 / 176543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (284197143 / 500000000) (568394287 / 1000000000) (Real.log (176543 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (176543 / 100000) = -Real.log (100000 / 176543) := by
    rw [show ((176543 / 100000) : ℝ) = ((100000 / 176543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1450001227 / 1000000000) ≤ -Real.log (23457 / 100000) ∧
    -Real.log (23457 / 100000) ≤ (145000123 / 100000000) := by
  have h := checkLog_sound (w := (1543 / 48457)) (n := 12)
    (lo := (63706867 / 1000000000)) (hi := (15926717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23457) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 23457) = 1/(23457 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-145000123 / 100000000) (-1450001227 / 1000000000) (Real.log (23457 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (123595847 / 250000000) ≤ -Real.log (1000000 / 1639487) ∧
    -Real.log (1000000 / 1639487) ≤ (494383389 / 1000000000) := by
  have h := checkLog_sound (w := (639487 / 2639487)) (n := 12)
    (lo := (123595847 / 250000000)) (hi := (494383389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1639487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1639487 / 1000000) = 1/(1000000 / 1639487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (123595847 / 250000000) (494383389 / 1000000000) (Real.log (1639487 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1639487 / 1000000) = -Real.log (1000000 / 1639487) := by
    rw [show ((1639487 / 1000000) : ℝ) = ((1000000 / 1639487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1020227261 / 1000000000) ≤ -Real.log (360513 / 1000000) ∧
    -Real.log (360513 / 1000000) ≤ (1020227263 / 1000000000) := by
  have h := checkLog_sound (w := (139487 / 860513)) (n := 12)
    (lo := (327080081 / 1000000000)) (hi := (163540041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360513) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 360513) = 1/(360513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1020227263 / 1000000000) (-1020227261 / 1000000000) (Real.log (360513 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (99292351 / 200000000) ≤ -Real.log (500000 / 821449) ∧
    -Real.log (500000 / 821449) ≤ (124115439 / 250000000) := by
  have h := checkLog_sound (w := (321449 / 1321449)) (n := 12)
    (lo := (99292351 / 200000000)) (hi := (124115439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821449 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821449 / 500000) = 1/(500000 / 821449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99292351 / 200000000) (124115439 / 250000000) (Real.log (821449 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (821449 / 500000) = -Real.log (500000 / 821449) := by
    rw [show ((821449 / 500000) : ℝ) = ((500000 / 821449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1029733823 / 1000000000) ≤ -Real.log (178551 / 500000) ∧
    -Real.log (178551 / 500000) ≤ (41189353 / 40000000) := by
  have h := checkLog_sound (w := (71449 / 428551)) (n := 12)
    (lo := (336586643 / 1000000000)) (hi := (84146661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178551) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 178551) = 1/(178551 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-41189353 / 40000000) (-1029733823 / 1000000000) (Real.log (178551 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (250464879 / 125000000) ≤ -Real.log (250000000000 / 1854146852617) ∧
    -Real.log (250000000000 / 1854146852617) ≤ (400743807 / 200000000) := by
  have h := checkLog_sound (w := (854146852617 / 2854146852617)) (n := 12)
    (lo := (19294521 / 31250000)) (hi := (617424673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1854146852617 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1854146852617 / 1000000000000) = 1/(250000000000 / 1854146852617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (250464879 / 125000000) (400743807 / 200000000) (Real.log (1854146852617 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1854146852617 / 250000000000) = -Real.log (250000000000 / 1854146852617) := by
    rw [show ((1854146852617 / 250000000000) : ℝ) = ((250000000000 / 1854146852617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2018395513 / 1000000000) ≤ -Real.log (250000000000 / 1881559875517) ∧
    -Real.log (250000000000 / 1881559875517) ≤ (504598879 / 250000000) := by
  have h := checkLog_sound (w := (881559875517 / 2881559875517)) (n := 12)
    (lo := (632101153 / 1000000000)) (hi := (316050577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881559875517 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1881559875517 / 1000000000000) = 1/(250000000000 / 1881559875517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2018395513 / 1000000000) (504598879 / 250000000) (Real.log (1881559875517 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1881559875517 / 250000000000) = -Real.log (250000000000 / 1881559875517) := by
    rw [show ((1881559875517 / 250000000000) : ℝ) = ((250000000000 / 1881559875517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (189326331 / 125000000) ≤ -Real.log (250000000000 / 1136912538521) ∧
    -Real.log (250000000000 / 1136912538521) ≤ (1514610651 / 1000000000) := by
  have h := checkLog_sound (w := (136912538521 / 2136912538521)) (n := 12)
    (lo := (1002471 / 7812500)) (hi := (128316289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136912538521 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1136912538521 / 1000000000000) = 1/(250000000000 / 1136912538521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (189326331 / 125000000) (1514610651 / 1000000000) (Real.log (1136912538521 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1136912538521 / 250000000000) = -Real.log (250000000000 / 1136912538521) := by
    rw [show ((1136912538521 / 250000000000) : ℝ) = ((250000000000 / 1136912538521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (763097789 / 500000000) ≤ -Real.log (500000000000 / 2300320356649) ∧
    -Real.log (500000000000 / 2300320356649) ≤ (1526195581 / 1000000000) := by
  have h := checkLog_sound (w := (300320356649 / 4300320356649)) (n := 12)
    (lo := (69950609 / 500000000)) (hi := (139901219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2300320356649 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2300320356649 / 2000000000000) = 1/(500000000000 / 2300320356649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (763097789 / 500000000) (1526195581 / 1000000000) (Real.log (2300320356649 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2300320356649 / 500000000000) = -Real.log (500000000000 / 2300320356649) := by
    rw [show ((2300320356649 / 500000000000) : ℝ) = ((500000000000 / 2300320356649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0015

end


