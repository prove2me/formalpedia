-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0066Logs__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0066Logs__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:53:33.791852+00:00
-- url     : https://prove2.me/theorems/a132604d-230c-48c4-91bc-2a802873010c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0066Logs (+2 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0067Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0068Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0066
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

theorem reflection_log_1_neg : (677552581 / 1000000000) ≤ -Real.log (102400 / 201631) ∧
    -Real.log (102400 / 201631) ≤ (338776291 / 500000000) := by
  have h := checkLog_sound (w := (99231 / 304031)) (n := 12)
    (lo := (677552581 / 1000000000)) (hi := (338776291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201631 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201631 / 102400) = 1/(102400 / 201631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (677552581 / 1000000000) (338776291 / 500000000) (Real.log (201631 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201631 / 102400) = -Real.log (102400 / 201631) := by
    rw [show ((201631 / 102400) : ℝ) = ((102400 / 201631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3475470629 / 1000000000) ≤ -Real.log (3169 / 102400) ∧
    -Real.log (3169 / 102400) ≤ (695094127 / 200000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3169) = 1/(3169 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-695094127 / 200000000) (-3475470629 / 1000000000) (Real.log (3169 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (135491669 / 200000000) ≤ -Real.log (25600 / 50403) ∧
    -Real.log (25600 / 50403) ≤ (338729173 / 500000000) := by
  have h := checkLog_sound (w := (24803 / 76003)) (n := 12)
    (lo := (135491669 / 200000000)) (hi := (338729173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50403 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50403 / 25600) = 1/(25600 / 50403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (135491669 / 200000000) (338729173 / 500000000) (Real.log (50403 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50403 / 25600) = -Real.log (25600 / 50403) := by
    rw [show ((50403 / 25600) : ℝ) = ((25600 / 50403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (867373237 / 250000000) ≤ -Real.log (797 / 25600) ∧
    -Real.log (797 / 25600) ≤ (1734746477 / 500000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 797) = 1/(797 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1734746477 / 500000000) (-867373237 / 250000000) (Real.log (797 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (661710933 / 1000000000) ≤ -Real.log (51200 / 99231) ∧
    -Real.log (51200 / 99231) ≤ (330855467 / 500000000) := by
  have h := checkLog_sound (w := (48031 / 150431)) (n := 12)
    (lo := (661710933 / 1000000000)) (hi := (330855467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99231 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99231 / 51200) = 1/(51200 / 99231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (661710933 / 1000000000) (330855467 / 500000000) (Real.log (99231 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99231 / 51200) = -Real.log (51200 / 99231) := by
    rw [show ((99231 / 51200) : ℝ) = ((51200 / 99231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2782323449 / 1000000000) ≤ -Real.log (3169 / 51200) ∧
    -Real.log (3169 / 51200) ≤ (1391161727 / 500000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3169) = 1/(3169 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1391161727 / 500000000) (-2782323449 / 1000000000) (Real.log (3169 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (330759721 / 500000000) ≤ -Real.log (12800 / 24803) ∧
    -Real.log (12800 / 24803) ≤ (661519443 / 1000000000) := by
  have h := checkLog_sound (w := (12003 / 37603)) (n := 12)
    (lo := (330759721 / 500000000)) (hi := (661519443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24803 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24803 / 12800) = 1/(12800 / 24803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (330759721 / 500000000) (661519443 / 1000000000) (Real.log (24803 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24803 / 12800) = -Real.log (12800 / 24803) := by
    rw [show ((24803 / 12800) : ℝ) = ((12800 / 24803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (347043221 / 125000000) ≤ -Real.log (797 / 12800) ∧
    -Real.log (797 / 12800) ≤ (2776345773 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 797) = 1/(797 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2776345773 / 1000000000) (-347043221 / 125000000) (Real.log (797 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340035783 / 500000000) ≤ -Real.log (1000000 / 1974019) ∧
    -Real.log (1000000 / 1974019) ≤ (680071567 / 1000000000) := by
  have h := checkLog_sound (w := (974019 / 2974019)) (n := 12)
    (lo := (340035783 / 500000000)) (hi := (680071567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974019 / 1000000) = 1/(1000000 / 1974019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340035783 / 500000000) (680071567 / 1000000000) (Real.log (1974019 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974019 / 1000000) = -Real.log (1000000 / 1974019) := by
    rw [show ((1974019 / 1000000) : ℝ) = ((1000000 / 1974019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1825194887 / 500000000) ≤ -Real.log (25981 / 1000000) ∧
    -Real.log (25981 / 1000000) ≤ (182519489 / 50000000) := by
  have h := checkLog_sound (w := (5269 / 57231)) (n := 12)
    (lo := (92326937 / 500000000)) (hi := (1477231 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25981) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25981) = 1/(25981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-182519489 / 50000000) (-1825194887 / 500000000) (Real.log (25981 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680146537 / 1000000000) ≤ -Real.log (1000000 / 1974167) ∧
    -Real.log (1000000 / 1974167) ≤ (340073269 / 500000000) := by
  have h := checkLog_sound (w := (974167 / 2974167)) (n := 12)
    (lo := (680146537 / 1000000000)) (hi := (340073269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974167 / 1000000) = 1/(1000000 / 1974167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680146537 / 1000000000) (340073269 / 500000000) (Real.log (1974167 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1974167 / 1000000) = -Real.log (1000000 / 1974167) := by
    rw [show ((1974167 / 1000000) : ℝ) = ((1000000 / 1974167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3656102531 / 1000000000) ≤ -Real.log (25833 / 1000000) ∧
    -Real.log (25833 / 1000000) ≤ (3656102537 / 1000000000) := by
  have h := checkLog_sound (w := (5417 / 57083)) (n := 12)
    (lo := (190366631 / 1000000000)) (hi := (23795829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25833) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25833) = 1/(25833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3656102537 / 1000000000) (-3656102531 / 1000000000) (Real.log (25833 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84998497 / 125000000) ≤ -Real.log (500000 / 986927) ∧
    -Real.log (500000 / 986927) ≤ (679987977 / 1000000000) := by
  have h := checkLog_sound (w := (486927 / 1486927)) (n := 12)
    (lo := (84998497 / 125000000)) (hi := (679987977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986927 / 500000) = 1/(500000 / 986927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84998497 / 125000000) (679987977 / 1000000000) (Real.log (986927 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (986927 / 500000) = -Real.log (500000 / 986927) := by
    rw [show ((986927 / 500000) : ℝ) = ((500000 / 986927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3644059061 / 1000000000) ≤ -Real.log (13073 / 500000) ∧
    -Real.log (13073 / 500000) ≤ (3644059067 / 1000000000) := by
  have h := checkLog_sound (w := (1276 / 14349)) (n := 12)
    (lo := (178323161 / 1000000000)) (hi := (89161581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13073) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13073) = 1/(13073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3644059067 / 1000000000) (-3644059061 / 1000000000) (Real.log (13073 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680064473 / 1000000000) ≤ -Real.log (200000 / 394801) ∧
    -Real.log (200000 / 394801) ≤ (340032237 / 500000000) := by
  have h := checkLog_sound (w := (194801 / 594801)) (n := 12)
    (lo := (680064473 / 1000000000)) (hi := (340032237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394801 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394801 / 200000) = 1/(200000 / 394801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680064473 / 1000000000) (340032237 / 500000000) (Real.log (394801 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (394801 / 200000) = -Real.log (200000 / 394801) := by
    rw [show ((394801 / 200000) : ℝ) = ((200000 / 394801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (456231383 / 125000000) ≤ -Real.log (5199 / 200000) ∧
    -Real.log (5199 / 200000) ≤ (364985107 / 100000000) := by
  have h := checkLog_sound (w := (1051 / 11449)) (n := 12)
    (lo := (46028791 / 250000000)) (hi := (36823033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5199) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5199) = 1/(5199 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-364985107 / 100000000) (-456231383 / 125000000) (Real.log (5199 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (216523067 / 50000000) ≤ -Real.log (250000000000 / 18994832762403) ∧
    -Real.log (250000000000 / 18994832762403) ≤ (4330461347 / 1000000000) := by
  have h := checkLog_sound (w := (2994832762403 / 34994832762403)) (n := 12)
    (lo := (8578913 / 50000000)) (hi := (171578261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18994832762403 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18994832762403 / 16000000000000) = 1/(250000000000 / 18994832762403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (216523067 / 50000000) (4330461347 / 1000000000) (Real.log (18994832762403 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18994832762403 / 250000000000) = -Real.log (250000000000 / 18994832762403) := by
    rw [show ((18994832762403 / 250000000000) : ℝ) = ((250000000000 / 18994832762403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1084062267 / 250000000) ≤ -Real.log (500000000000 / 38210176905509) ∧
    -Real.log (500000000000 / 38210176905509) ≤ (173449963 / 40000000) := by
  have h := checkLog_sound (w := (6210176905509 / 70210176905509)) (n := 12)
    (lo := (44341497 / 250000000)) (hi := (177365989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38210176905509 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38210176905509 / 32000000000000) = 1/(500000000000 / 38210176905509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1084062267 / 250000000) (173449963 / 40000000) (Real.log (38210176905509 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (38210176905509 / 500000000000) = -Real.log (500000000000 / 38210176905509) := by
    rw [show ((38210176905509 / 500000000000) : ℝ) = ((500000000000 / 38210176905509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4324047037 / 1000000000) ≤ -Real.log (500000000000 / 37746768148091) ∧
    -Real.log (500000000000 / 37746768148091) ≤ (1081011761 / 250000000) := by
  have h := checkLog_sound (w := (5746768148091 / 69746768148091)) (n := 12)
    (lo := (165163957 / 1000000000)) (hi := (82581979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37746768148091 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37746768148091 / 32000000000000) = 1/(500000000000 / 37746768148091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4324047037 / 1000000000) (1081011761 / 250000000) (Real.log (37746768148091 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (37746768148091 / 500000000000) = -Real.log (500000000000 / 37746768148091) := by
    rw [show ((37746768148091 / 500000000000) : ℝ) = ((500000000000 / 37746768148091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4329915537 / 1000000000) ≤ -Real.log (500000000000 / 37968936333911) ∧
    -Real.log (500000000000 / 37968936333911) ≤ (541239443 / 125000000) := by
  have h := checkLog_sound (w := (5968936333911 / 69968936333911)) (n := 12)
    (lo := (171032457 / 1000000000)) (hi := (85516229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37968936333911 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37968936333911 / 32000000000000) = 1/(500000000000 / 37968936333911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4329915537 / 1000000000) (541239443 / 125000000) (Real.log (37968936333911 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (37968936333911 / 500000000000) = -Real.log (500000000000 / 37968936333911) := by
    rw [show ((37968936333911 / 500000000000) : ℝ) = ((500000000000 / 37968936333911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0066

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0067
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

theorem reflection_log_1_neg : (135491669 / 200000000) ≤ -Real.log (25600 / 50403) ∧
    -Real.log (25600 / 50403) ≤ (338729173 / 500000000) := by
  have h := checkLog_sound (w := (24803 / 76003)) (n := 12)
    (lo := (135491669 / 200000000)) (hi := (338729173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50403 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50403 / 25600) = 1/(25600 / 50403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (135491669 / 200000000) (338729173 / 500000000) (Real.log (50403 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50403 / 25600) = -Real.log (25600 / 50403) := by
    rw [show ((50403 / 25600) : ℝ) = ((25600 / 50403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (867373237 / 250000000) ≤ -Real.log (797 / 25600) ∧
    -Real.log (797 / 25600) ≤ (1734746477 / 500000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 797) = 1/(797 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1734746477 / 500000000) (-867373237 / 250000000) (Real.log (797 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (6773641 / 10000000) ≤ -Real.log (102400 / 201593) ∧
    -Real.log (102400 / 201593) ≤ (677364101 / 1000000000) := by
  have h := checkLog_sound (w := (99193 / 303993)) (n := 12)
    (lo := (6773641 / 10000000)) (hi := (677364101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201593 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201593 / 102400) = 1/(102400 / 201593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (6773641 / 10000000) (677364101 / 1000000000) (Real.log (201593 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201593 / 102400) = -Real.log (102400 / 201593) := by
    rw [show ((201593 / 102400) : ℝ) = ((102400 / 201593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3463550789 / 1000000000) ≤ -Real.log (3207 / 102400) ∧
    -Real.log (3207 / 102400) ≤ (1731775397 / 500000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 3207) = 1/(3207 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1731775397 / 500000000) (-3463550789 / 1000000000) (Real.log (3207 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (330759721 / 500000000) ≤ -Real.log (12800 / 24803) ∧
    -Real.log (12800 / 24803) ≤ (661519443 / 1000000000) := by
  have h := checkLog_sound (w := (12003 / 37603)) (n := 12)
    (lo := (330759721 / 500000000)) (hi := (661519443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24803 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24803 / 12800) = 1/(12800 / 24803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (330759721 / 500000000) (661519443 / 1000000000) (Real.log (24803 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24803 / 12800) = -Real.log (12800 / 24803) := by
    rw [show ((24803 / 12800) : ℝ) = ((12800 / 24803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (347043221 / 125000000) ≤ -Real.log (797 / 12800) ∧
    -Real.log (797 / 12800) ≤ (2776345773 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 797) = 1/(797 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2776345773 / 1000000000) (-347043221 / 125000000) (Real.log (797 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (132265583 / 200000000) ≤ -Real.log (51200 / 99193) ∧
    -Real.log (51200 / 99193) ≤ (165331979 / 250000000) := by
  have h := checkLog_sound (w := (47993 / 150393)) (n := 12)
    (lo := (132265583 / 200000000)) (hi := (165331979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99193 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99193 / 51200) = 1/(51200 / 99193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (132265583 / 200000000) (165331979 / 250000000) (Real.log (99193 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99193 / 51200) = -Real.log (51200 / 99193) := by
    rw [show ((99193 / 51200) : ℝ) = ((51200 / 99193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2770403609 / 1000000000) ≤ -Real.log (3207 / 51200) ∧
    -Real.log (3207 / 51200) ≤ (2770403613 / 1000000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6400 / 3207) = 1/(3207 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2770403613 / 1000000000) (-2770403609 / 1000000000) (Real.log (3207 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135999419 / 200000000) ≤ -Real.log (62500 / 123367) ∧
    -Real.log (62500 / 123367) ≤ (84999637 / 125000000) := by
  have h := checkLog_sound (w := (60867 / 185867)) (n := 12)
    (lo := (135999419 / 200000000)) (hi := (84999637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123367 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123367 / 62500) = 1/(62500 / 123367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135999419 / 200000000) (84999637 / 125000000) (Real.log (123367 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (123367 / 62500) = -Real.log (62500 / 123367) := by
    rw [show ((123367 / 62500) : ℝ) = ((62500 / 123367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3644747739 / 1000000000) ≤ -Real.log (1633 / 62500) ∧
    -Real.log (1633 / 62500) ≤ (728949549 / 200000000) := by
  have h := checkLog_sound (w := (2561 / 28689)) (n := 12)
    (lo := (179011839 / 1000000000)) (hi := (139853 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13064) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13064) = 1/(1633 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-728949549 / 200000000) (-3644747739 / 1000000000) (Real.log (1633 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85009009 / 125000000) ≤ -Real.log (50000 / 98701) ∧
    -Real.log (50000 / 98701) ≤ (680072073 / 1000000000) := by
  have h := checkLog_sound (w := (48701 / 148701)) (n := 12)
    (lo := (85009009 / 125000000)) (hi := (680072073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98701 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98701 / 50000) = 1/(50000 / 98701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85009009 / 125000000) (680072073 / 1000000000) (Real.log (98701 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98701 / 50000) = -Real.log (50000 / 98701) := by
    rw [show ((98701 / 50000) : ℝ) = ((50000 / 98701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (456303533 / 125000000) ≤ -Real.log (1299 / 50000) ∧
    -Real.log (1299 / 50000) ≤ (365042827 / 100000000) := by
  have h := checkLog_sound (w := (527 / 5723)) (n := 12)
    (lo := (46173091 / 250000000)) (hi := (36938473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2598) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2598) = 1/(1299 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-365042827 / 100000000) (-456303533 / 125000000) (Real.log (1299 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679912487 / 1000000000) ≤ -Real.log (200000 / 394741) ∧
    -Real.log (200000 / 394741) ≤ (84989061 / 125000000) := by
  have h := checkLog_sound (w := (194741 / 594741)) (n := 12)
    (lo := (679912487 / 1000000000)) (hi := (84989061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394741 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394741 / 200000) = 1/(200000 / 394741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679912487 / 1000000000) (84989061 / 125000000) (Real.log (394741 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (394741 / 200000) = -Real.log (200000 / 394741) := by
    rw [show ((394741 / 200000) : ℝ) = ((200000 / 394741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3638376469 / 1000000000) ≤ -Real.log (5259 / 200000) ∧
    -Real.log (5259 / 200000) ≤ (145535059 / 40000000) := by
  have h := checkLog_sound (w := (991 / 11509)) (n := 12)
    (lo := (172640569 / 1000000000)) (hi := (17264057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5259) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5259) = 1/(5259 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-145535059 / 40000000) (-3638376469 / 1000000000) (Real.log (5259 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679988483 / 1000000000) ≤ -Real.log (200000 / 394771) ∧
    -Real.log (200000 / 394771) ≤ (169997121 / 250000000) := by
  have h := checkLog_sound (w := (194771 / 594771)) (n := 12)
    (lo := (679988483 / 1000000000)) (hi := (169997121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394771 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394771 / 200000) = 1/(200000 / 394771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679988483 / 1000000000) (169997121 / 250000000) (Real.log (394771 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (394771 / 200000) = -Real.log (200000 / 394771) := by
    rw [show ((394771 / 200000) : ℝ) = ((200000 / 394771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (911024327 / 250000000) ≤ -Real.log (5229 / 200000) ∧
    -Real.log (5229 / 200000) ≤ (1822048657 / 500000000) := by
  have h := checkLog_sound (w := (1021 / 11479)) (n := 12)
    (lo := (2786897 / 15625000)) (hi := (178361409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5229) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5229) = 1/(5229 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1822048657 / 500000000) (-911024327 / 250000000) (Real.log (5229 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (864948967 / 200000000) ≤ -Real.log (100000000000 / 7554623392529) ∧
    -Real.log (100000000000 / 7554623392529) ≤ (2162372421 / 500000000) := by
  have h := checkLog_sound (w := (1154623392529 / 13954623392529)) (n := 12)
    (lo := (33172351 / 200000000)) (hi := (41465439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7554623392529 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7554623392529 / 6400000000000) = 1/(100000000000 / 7554623392529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (864948967 / 200000000) (2162372421 / 500000000) (Real.log (7554623392529 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7554623392529 / 100000000000) = -Real.log (100000000000 / 7554623392529) := by
    rw [show ((7554623392529 / 100000000000) : ℝ) = ((100000000000 / 7554623392529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4330500337 / 1000000000) ≤ -Real.log (250000000000 / 18995573518091) ∧
    -Real.log (250000000000 / 18995573518091) ≤ (541312543 / 125000000) := by
  have h := checkLog_sound (w := (2995573518091 / 34995573518091)) (n := 12)
    (lo := (171617257 / 1000000000)) (hi := (85808629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18995573518091 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18995573518091 / 16000000000000) = 1/(250000000000 / 18995573518091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4330500337 / 1000000000) (541312543 / 125000000) (Real.log (18995573518091 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (18995573518091 / 250000000000) = -Real.log (250000000000 / 18995573518091) := by
    rw [show ((18995573518091 / 250000000000) : ℝ) = ((250000000000 / 18995573518091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (863657791 / 200000000) ≤ -Real.log (10000000000 / 750600874691) ∧
    -Real.log (10000000000 / 750600874691) ≤ (2159144481 / 500000000) := by
  have h := checkLog_sound (w := (110600874691 / 1390600874691)) (n := 12)
    (lo := (1275247 / 8000000)) (hi := (39851469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750600874691 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(750600874691 / 640000000000) = 1/(10000000000 / 750600874691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (863657791 / 200000000) (2159144481 / 500000000) (Real.log (750600874691 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (750600874691 / 10000000000) = -Real.log (10000000000 / 750600874691) := by
    rw [show ((750600874691 / 10000000000) : ℝ) = ((10000000000 / 750600874691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4324085791 / 1000000000) ≤ -Real.log (125000000000 / 9437057754829) ∧
    -Real.log (125000000000 / 9437057754829) ≤ (2162042899 / 500000000) := by
  have h := checkLog_sound (w := (1437057754829 / 17437057754829)) (n := 12)
    (lo := (165202711 / 1000000000)) (hi := (20650339 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9437057754829 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9437057754829 / 8000000000000) = 1/(125000000000 / 9437057754829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4324085791 / 1000000000) (2162042899 / 500000000) (Real.log (9437057754829 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9437057754829 / 125000000000) = -Real.log (125000000000 / 9437057754829) := by
    rw [show ((9437057754829 / 125000000000) : ℝ) = ((125000000000 / 9437057754829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0067

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0068
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

theorem reflection_log_1_neg : (6773641 / 10000000) ≤ -Real.log (102400 / 201593) ∧
    -Real.log (102400 / 201593) ≤ (677364101 / 1000000000) := by
  have h := checkLog_sound (w := (99193 / 303993)) (n := 12)
    (lo := (6773641 / 10000000)) (hi := (677364101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201593 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201593 / 102400) = 1/(102400 / 201593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (6773641 / 10000000) (677364101 / 1000000000) (Real.log (201593 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201593 / 102400) = -Real.log (102400 / 201593) := by
    rw [show ((201593 / 102400) : ℝ) = ((102400 / 201593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3463550789 / 1000000000) ≤ -Real.log (3207 / 102400) ∧
    -Real.log (3207 / 102400) ≤ (1731775397 / 500000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 3207) = 1/(3207 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1731775397 / 500000000) (-3463550789 / 1000000000) (Real.log (3207 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (677269847 / 1000000000) ≤ -Real.log (51200 / 100787) ∧
    -Real.log (51200 / 100787) ≤ (84658731 / 125000000) := by
  have h := checkLog_sound (w := (49587 / 151987)) (n := 12)
    (lo := (677269847 / 1000000000)) (hi := (84658731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100787 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100787 / 51200) = 1/(51200 / 100787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (677269847 / 1000000000) (84658731 / 125000000) (Real.log (100787 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100787 / 51200) = -Real.log (51200 / 100787) := by
    rw [show ((100787 / 51200) : ℝ) = ((51200 / 100787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (345764373 / 100000000) ≤ -Real.log (1613 / 51200) ∧
    -Real.log (1613 / 51200) ≤ (691528747 / 200000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1613) = 1/(1613 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-691528747 / 200000000) (-345764373 / 100000000) (Real.log (1613 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (132265583 / 200000000) ≤ -Real.log (51200 / 99193) ∧
    -Real.log (51200 / 99193) ≤ (165331979 / 250000000) := by
  have h := checkLog_sound (w := (47993 / 150393)) (n := 12)
    (lo := (132265583 / 200000000)) (hi := (165331979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99193 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99193 / 51200) = 1/(51200 / 99193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (132265583 / 200000000) (165331979 / 250000000) (Real.log (99193 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99193 / 51200) = -Real.log (51200 / 99193) := by
    rw [show ((99193 / 51200) : ℝ) = ((51200 / 99193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2770403609 / 1000000000) ≤ -Real.log (3207 / 51200) ∧
    -Real.log (3207 / 51200) ≤ (2770403613 / 1000000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6400 / 3207) = 1/(3207 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2770403613 / 1000000000) (-2770403609 / 1000000000) (Real.log (3207 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (661136351 / 1000000000) ≤ -Real.log (25600 / 49587) ∧
    -Real.log (25600 / 49587) ≤ (20660511 / 31250000) := by
  have h := checkLog_sound (w := (23987 / 75187)) (n := 12)
    (lo := (661136351 / 1000000000)) (hi := (20660511 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49587 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49587 / 25600) = 1/(25600 / 49587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (661136351 / 1000000000) (20660511 / 31250000) (Real.log (49587 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49587 / 25600) = -Real.log (25600 / 49587) := by
    rw [show ((49587 / 25600) : ℝ) = ((25600 / 49587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (55289931 / 20000000) ≤ -Real.log (1613 / 25600) ∧
    -Real.log (1613 / 25600) ≤ (1382248277 / 500000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1613) = 1/(1613 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1382248277 / 500000000) (-55289931 / 20000000) (Real.log (1613 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33996131 / 50000000) ≤ -Real.log (40000 / 78949) ∧
    -Real.log (40000 / 78949) ≤ (679922621 / 1000000000) := by
  have h := checkLog_sound (w := (38949 / 118949)) (n := 12)
    (lo := (33996131 / 50000000)) (hi := (679922621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78949 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78949 / 40000) = 1/(40000 / 78949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33996131 / 50000000) (679922621 / 1000000000) (Real.log (78949 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78949 / 40000) = -Real.log (40000 / 78949) := by
    rw [show ((78949 / 40000) : ℝ) = ((40000 / 78949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3639137359 / 1000000000) ≤ -Real.log (1051 / 40000) ∧
    -Real.log (1051 / 40000) ≤ (727827473 / 200000000) := by
  have h := checkLog_sound (w := (199 / 2301)) (n := 12)
    (lo := (173401459 / 1000000000)) (hi := (8670073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1051) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 1051) = 1/(1051 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-727827473 / 200000000) (-3639137359 / 1000000000) (Real.log (1051 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339998801 / 500000000) ≤ -Real.log (1000000 / 1973873) ∧
    -Real.log (1000000 / 1973873) ≤ (679997603 / 1000000000) := by
  have h := checkLog_sound (w := (973873 / 2973873)) (n := 12)
    (lo := (339998801 / 500000000)) (hi := (679997603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973873 / 1000000) = 1/(1000000 / 1973873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339998801 / 500000000) (679997603 / 1000000000) (Real.log (1973873 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1973873 / 1000000) = -Real.log (1000000 / 1973873) := by
    rw [show ((1973873 / 1000000) : ℝ) = ((1000000 / 1973873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3644786013 / 1000000000) ≤ -Real.log (26127 / 1000000) ∧
    -Real.log (26127 / 1000000) ≤ (3644786019 / 1000000000) := by
  have h := checkLog_sound (w := (5123 / 57377)) (n := 12)
    (lo := (179050113 / 1000000000)) (hi := (89525057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26127) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26127) = 1/(26127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3644786019 / 1000000000) (-3644786013 / 1000000000) (Real.log (26127 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135967297 / 200000000) ≤ -Real.log (200000 / 394711) ∧
    -Real.log (200000 / 394711) ≤ (339918243 / 500000000) := by
  have h := checkLog_sound (w := (194711 / 594711)) (n := 12)
    (lo := (135967297 / 200000000)) (hi := (339918243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394711 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394711 / 200000) = 1/(200000 / 394711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135967297 / 200000000) (339918243 / 500000000) (Real.log (394711 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (394711 / 200000) = -Real.log (200000 / 394711) := by
    rw [show ((394711 / 200000) : ℝ) = ((200000 / 394711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3632688171 / 1000000000) ≤ -Real.log (5289 / 200000) ∧
    -Real.log (5289 / 200000) ≤ (3632688177 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 11539)) (n := 12)
    (lo := (166952271 / 1000000000)) (hi := (10434517 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5289) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5289) = 1/(5289 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3632688177 / 1000000000) (-3632688171 / 1000000000) (Real.log (5289 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679912993 / 1000000000) ≤ -Real.log (500000 / 986853) ∧
    -Real.log (500000 / 986853) ≤ (339956497 / 500000000) := by
  have h := checkLog_sound (w := (486853 / 1486853)) (n := 12)
    (lo := (679912993 / 1000000000)) (hi := (339956497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986853 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986853 / 500000) = 1/(500000 / 986853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679912993 / 1000000000) (339956497 / 500000000) (Real.log (986853 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (986853 / 500000) = -Real.log (500000 / 986853) := by
    rw [show ((986853 / 500000) : ℝ) = ((500000 / 986853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3638414499 / 1000000000) ≤ -Real.log (13147 / 500000) ∧
    -Real.log (13147 / 500000) ≤ (727682901 / 200000000) := by
  have h := checkLog_sound (w := (1239 / 14386)) (n := 12)
    (lo := (172678599 / 1000000000)) (hi := (863393 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13147) = 1/(13147 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-727682901 / 200000000) (-3638414499 / 1000000000) (Real.log (13147 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4319059979 / 1000000000) ≤ -Real.log (250000000000 / 18779495718363) ∧
    -Real.log (250000000000 / 18779495718363) ≤ (2159529993 / 500000000) := by
  have h := checkLog_sound (w := (2779495718363 / 34779495718363)) (n := 12)
    (lo := (160176899 / 1000000000)) (hi := (1601769 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18779495718363 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18779495718363 / 16000000000000) = 1/(250000000000 / 18779495718363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4319059979 / 1000000000) (2159529993 / 500000000) (Real.log (18779495718363 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18779495718363 / 250000000000) = -Real.log (250000000000 / 18779495718363) := by
    rw [show ((18779495718363 / 250000000000) : ℝ) = ((250000000000 / 18779495718363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (864956723 / 200000000) ≤ -Real.log (250000000000 / 18887290925097) ∧
    -Real.log (250000000000 / 18887290925097) ≤ (2162391811 / 500000000) := by
  have h := checkLog_sound (w := (2887290925097 / 34887290925097)) (n := 12)
    (lo := (33180107 / 200000000)) (hi := (20737567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18887290925097 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18887290925097 / 16000000000000) = 1/(250000000000 / 18887290925097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (864956723 / 200000000) (2162391811 / 500000000) (Real.log (18887290925097 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (18887290925097 / 250000000000) = -Real.log (250000000000 / 18887290925097) := by
    rw [show ((18887290925097 / 250000000000) : ℝ) = ((250000000000 / 18887290925097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (269532791 / 62500000) ≤ -Real.log (62500000000 / 4664291453961) ∧
    -Real.log (62500000000 / 4664291453961) ≤ (4312524663 / 1000000000) := by
  have h := checkLog_sound (w := (664291453961 / 8664291453961)) (n := 12)
    (lo := (19205197 / 125000000)) (hi := (153641577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4664291453961 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4664291453961 / 4000000000000) = 1/(62500000000 / 4664291453961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (269532791 / 62500000) (4312524663 / 1000000000) (Real.log (4664291453961 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4664291453961 / 62500000000) = -Real.log (62500000000 / 4664291453961) := by
    rw [show ((4664291453961 / 62500000000) : ℝ) = ((62500000000 / 4664291453961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4318327493 / 1000000000) ≤ -Real.log (250000000000 / 18765745036891) ∧
    -Real.log (250000000000 / 18765745036891) ≤ (1727331 / 400000) := by
  have h := checkLog_sound (w := (2765745036891 / 34765745036891)) (n := 12)
    (lo := (159444413 / 1000000000)) (hi := (79722207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18765745036891 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18765745036891 / 16000000000000) = 1/(250000000000 / 18765745036891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4318327493 / 1000000000) (1727331 / 400000) (Real.log (18765745036891 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18765745036891 / 250000000000) = -Real.log (250000000000 / 18765745036891) := by
    rw [show ((18765745036891 / 250000000000) : ℝ) = ((250000000000 / 18765745036891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0068

end


