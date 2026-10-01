-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0019Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0019Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:45:27.377849+00:00
-- url     : https://prove2.me/theorems/353360c9-226e-4a58-ae5d-be4fd6b2faf5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0019Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0020Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0019Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0020Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0021Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0022Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0023Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0024Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0025Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0019Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0020Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0021Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0022Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0023Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0024Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0025Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0019Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0020Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0021Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0022Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0023Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0024Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0025Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0019Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0020Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0021Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0022Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0023Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0024Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0025Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0019Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0019
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

theorem reflection_log_1_neg : (136394337 / 200000000) ≤ -Real.log (25600 / 50631) ∧
    -Real.log (25600 / 50631) ≤ (340985843 / 500000000) := by
  have h := checkLog_sound (w := (25031 / 76231)) (n := 12)
    (lo := (136394337 / 200000000)) (hi := (340985843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50631 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50631 / 25600) = 1/(25600 / 50631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136394337 / 200000000) (340985843 / 500000000) (Real.log (50631 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50631 / 25600) = -Real.log (25600 / 50631) := by
    rw [show ((50631 / 25600) : ℝ) = ((25600 / 50631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3806467193 / 1000000000) ≤ -Real.log (569 / 25600) ∧
    -Real.log (569 / 25600) ≤ (3806467199 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 569) = 1/(569 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3806467199 / 1000000000) (-3806467193 / 1000000000) (Real.log (569 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (85234733 / 125000000) ≤ -Real.log (20480 / 40501) ∧
    -Real.log (20480 / 40501) ≤ (136375573 / 200000000) := by
  have h := checkLog_sound (w := (20021 / 60981)) (n := 12)
    (lo := (85234733 / 125000000)) (hi := (136375573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40501 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40501 / 20480) = 1/(20480 / 40501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (85234733 / 125000000) (136375573 / 200000000) (Real.log (40501 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40501 / 20480) = -Real.log (20480 / 40501) := by
    rw [show ((40501 / 20480) : ℝ) = ((20480 / 40501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1899076933 / 500000000) ≤ -Real.log (459 / 20480) ∧
    -Real.log (459 / 20480) ≤ (237384617 / 62500000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 459) = 1/(459 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-237384617 / 62500000) (-1899076933 / 500000000) (Real.log (459 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (134133977 / 200000000) ≤ -Real.log (12800 / 25031) ∧
    -Real.log (12800 / 25031) ≤ (335334943 / 500000000) := by
  have h := checkLog_sound (w := (12231 / 37831)) (n := 12)
    (lo := (134133977 / 200000000)) (hi := (335334943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25031 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25031 / 12800) = 1/(12800 / 25031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (134133977 / 200000000) (335334943 / 500000000) (Real.log (25031 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (25031 / 12800) = -Real.log (12800 / 25031) := by
    rw [show ((25031 / 12800) : ℝ) = ((12800 / 25031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3113320013 / 1000000000) ≤ -Real.log (569 / 12800) ∧
    -Real.log (569 / 12800) ≤ (1556660009 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 569) = 1/(569 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1556660009 / 500000000) (-3113320013 / 1000000000) (Real.log (569 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (670480103 / 1000000000) ≤ -Real.log (10240 / 20021) ∧
    -Real.log (10240 / 20021) ≤ (83810013 / 125000000) := by
  have h := checkLog_sound (w := (9781 / 30261)) (n := 12)
    (lo := (670480103 / 1000000000)) (hi := (83810013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20021 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20021 / 10240) = 1/(10240 / 20021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (670480103 / 1000000000) (83810013 / 125000000) (Real.log (20021 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (20021 / 10240) = -Real.log (10240 / 20021) := by
    rw [show ((20021 / 10240) : ℝ) = ((10240 / 20021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1552503343 / 500000000) ≤ -Real.log (459 / 10240) ∧
    -Real.log (459 / 10240) ≤ (3105006691 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 459) = 1/(459 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3105006691 / 1000000000) (-1552503343 / 500000000) (Real.log (459 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42725773 / 62500000) ≤ -Real.log (1000000 / 1981021) ∧
    -Real.log (1000000 / 1981021) ≤ (683612369 / 1000000000) := by
  have h := checkLog_sound (w := (981021 / 2981021)) (n := 12)
    (lo := (42725773 / 62500000)) (hi := (683612369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981021 / 1000000) = 1/(1000000 / 1981021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42725773 / 62500000) (683612369 / 1000000000) (Real.log (1981021 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1981021 / 1000000) = -Real.log (1000000 / 1981021) := by
    rw [show ((1981021 / 1000000) : ℝ) = ((1000000 / 1981021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3964422171 / 1000000000) ≤ -Real.log (18979 / 1000000) ∧
    -Real.log (18979 / 1000000) ≤ (3964422177 / 1000000000) := by
  have h := checkLog_sound (w := (12271 / 50229)) (n := 12)
    (lo := (498686271 / 1000000000)) (hi := (7791973 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18979) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18979) = 1/(18979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3964422177 / 1000000000) (-3964422171 / 1000000000) (Real.log (18979 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170922147 / 250000000) ≤ -Real.log (250000 / 495293) ∧
    -Real.log (250000 / 495293) ≤ (683688589 / 1000000000) := by
  have h := checkLog_sound (w := (245293 / 745293)) (n := 12)
    (lo := (170922147 / 250000000)) (hi := (683688589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495293 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495293 / 250000) = 1/(250000 / 495293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170922147 / 250000000) (683688589 / 1000000000) (Real.log (495293 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495293 / 250000) = -Real.log (250000 / 495293) := by
    rw [show ((495293 / 250000) : ℝ) = ((250000 / 495293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (496551269 / 125000000) ≤ -Real.log (4707 / 250000) ∧
    -Real.log (4707 / 250000) ≤ (1986205079 / 500000000) := by
  have h := checkLog_sound (w := (6211 / 25039)) (n := 12)
    (lo := (126668563 / 250000000)) (hi := (506674253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9414) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9414) = 1/(4707 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1986205079 / 500000000) (-496551269 / 125000000) (Real.log (4707 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42723249 / 62500000) ≤ -Real.log (1000000 / 1980941) ∧
    -Real.log (1000000 / 1980941) ≤ (136714397 / 200000000) := by
  have h := checkLog_sound (w := (980941 / 2980941)) (n := 12)
    (lo := (42723249 / 62500000)) (hi := (136714397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980941 / 1000000) = 1/(1000000 / 1980941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42723249 / 62500000) (136714397 / 200000000) (Real.log (1980941 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980941 / 1000000) = -Real.log (1000000 / 1980941) := by
    rw [show ((1980941 / 1000000) : ℝ) = ((1000000 / 1980941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (792043169 / 200000000) ≤ -Real.log (19059 / 1000000) ∧
    -Real.log (19059 / 1000000) ≤ (3960215851 / 1000000000) := by
  have h := checkLog_sound (w := (12191 / 50309)) (n := 12)
    (lo := (98895989 / 200000000)) (hi := (247239973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19059) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19059) = 1/(19059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3960215851 / 1000000000) (-792043169 / 200000000) (Real.log (19059 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (341824861 / 500000000) ≤ -Real.log (200000 / 396219) ∧
    -Real.log (200000 / 396219) ≤ (683649723 / 1000000000) := by
  have h := checkLog_sound (w := (196219 / 596219)) (n := 12)
    (lo := (341824861 / 500000000)) (hi := (683649723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396219 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396219 / 200000) = 1/(200000 / 396219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (341824861 / 500000000) (683649723 / 1000000000) (Real.log (396219 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (396219 / 200000) = -Real.log (200000 / 396219) := by
    rw [show ((396219 / 200000) : ℝ) = ((200000 / 396219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1984164419 / 500000000) ≤ -Real.log (3781 / 200000) ∧
    -Real.log (3781 / 200000) ≤ (992082211 / 250000000) := by
  have h := checkLog_sound (w := (2469 / 10031)) (n := 12)
    (lo := (251296469 / 500000000)) (hi := (502592939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3781) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3781) = 1/(3781 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-992082211 / 250000000) (-1984164419 / 500000000) (Real.log (3781 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4648034539 / 1000000000) ≤ -Real.log (500000000000 / 52189815058749) ∧
    -Real.log (500000000000 / 52189815058749) ≤ (2324017273 / 500000000) := by
  have h := checkLog_sound (w := (20189815058749 / 84189815058749)) (n := 12)
    (lo := (489151459 / 1000000000)) (hi := (24457573 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52189815058749 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52189815058749 / 32000000000000) = 1/(500000000000 / 52189815058749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4648034539 / 1000000000) (2324017273 / 500000000) (Real.log (52189815058749 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (52189815058749 / 500000000000) = -Real.log (500000000000 / 52189815058749) := by
    rw [show ((52189815058749 / 500000000000) : ℝ) = ((500000000000 / 52189815058749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (232804937 / 50000000) ≤ -Real.log (500000000000 / 52612385808371) ∧
    -Real.log (500000000000 / 52612385808371) ≤ (4656098747 / 1000000000) := by
  have h := checkLog_sound (w := (20612385808371 / 84612385808371)) (n := 12)
    (lo := (24860783 / 50000000)) (hi := (497215661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52612385808371 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52612385808371 / 32000000000000) = 1/(500000000000 / 52612385808371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (232804937 / 50000000) (4656098747 / 1000000000) (Real.log (52612385808371 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (52612385808371 / 500000000000) = -Real.log (500000000000 / 52612385808371) := by
    rw [show ((52612385808371 / 500000000000) : ℝ) = ((500000000000 / 52612385808371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4643787829 / 1000000000) ≤ -Real.log (100000000000 / 10393729996327) ∧
    -Real.log (100000000000 / 10393729996327) ≤ (1160946959 / 250000000) := by
  have h := checkLog_sound (w := (3993729996327 / 16793729996327)) (n := 12)
    (lo := (484904749 / 1000000000)) (hi := (1939619 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10393729996327 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10393729996327 / 6400000000000) = 1/(100000000000 / 10393729996327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4643787829 / 1000000000) (1160946959 / 250000000) (Real.log (10393729996327 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10393729996327 / 100000000000) = -Real.log (100000000000 / 10393729996327) := by
    rw [show ((10393729996327 / 100000000000) : ℝ) = ((100000000000 / 10393729996327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14537433 / 3125000) ≤ -Real.log (500000000000 / 52396059243587) ∧
    -Real.log (500000000000 / 52396059243587) ≤ (4651978567 / 1000000000) := by
  have h := checkLog_sound (w := (20396059243587 / 84396059243587)) (n := 12)
    (lo := (12327387 / 25000000)) (hi := (493095481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52396059243587 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52396059243587 / 32000000000000) = 1/(500000000000 / 52396059243587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14537433 / 3125000) (4651978567 / 1000000000) (Real.log (52396059243587 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (52396059243587 / 500000000000) = -Real.log (500000000000 / 52396059243587) := by
    rw [show ((52396059243587 / 500000000000) : ℝ) = ((500000000000 / 52396059243587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0019

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0020Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0020
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

theorem reflection_log_1_neg : (85234733 / 125000000) ≤ -Real.log (20480 / 40501) ∧
    -Real.log (20480 / 40501) ≤ (136375573 / 200000000) := by
  have h := checkLog_sound (w := (20021 / 60981)) (n := 12)
    (lo := (85234733 / 125000000)) (hi := (136375573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40501 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40501 / 20480) = 1/(20480 / 40501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (85234733 / 125000000) (136375573 / 200000000) (Real.log (40501 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40501 / 20480) = -Real.log (20480 / 40501) := by
    rw [show ((40501 / 20480) : ℝ) = ((20480 / 40501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1899076933 / 500000000) ≤ -Real.log (459 / 20480) ∧
    -Real.log (459 / 20480) ≤ (237384617 / 62500000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 459) = 1/(459 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237384617 / 62500000) (-1899076933 / 500000000) (Real.log (459 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136356807 / 200000000) ≤ -Real.log (51200 / 101243) ∧
    -Real.log (51200 / 101243) ≤ (170446009 / 250000000) := by
  have h := checkLog_sound (w := (50043 / 152443)) (n := 12)
    (lo := (136356807 / 200000000)) (hi := (170446009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101243 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101243 / 51200) = 1/(51200 / 101243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136356807 / 200000000) (170446009 / 250000000) (Real.log (101243 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101243 / 51200) = -Real.log (51200 / 101243) := by
    rw [show ((101243 / 51200) : ℝ) = ((51200 / 101243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3789909081 / 1000000000) ≤ -Real.log (1157 / 51200) ∧
    -Real.log (1157 / 51200) ≤ (3789909087 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1157) = 1/(1157 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3789909087 / 1000000000) (-3789909081 / 1000000000) (Real.log (1157 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (670480103 / 1000000000) ≤ -Real.log (10240 / 20021) ∧
    -Real.log (10240 / 20021) ≤ (83810013 / 125000000) := by
  have h := checkLog_sound (w := (9781 / 30261)) (n := 12)
    (lo := (670480103 / 1000000000)) (hi := (83810013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20021 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20021 / 10240) = 1/(10240 / 20021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (670480103 / 1000000000) (83810013 / 125000000) (Real.log (20021 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (20021 / 10240) = -Real.log (10240 / 20021) := by
    rw [show ((20021 / 10240) : ℝ) = ((10240 / 20021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1552503343 / 500000000) ≤ -Real.log (459 / 10240) ∧
    -Real.log (459 / 10240) ≤ (3105006691 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 459) = 1/(459 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3105006691 / 1000000000) (-1552503343 / 500000000) (Real.log (459 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167572571 / 250000000) ≤ -Real.log (25600 / 50043) ∧
    -Real.log (25600 / 50043) ≤ (134058057 / 200000000) := by
  have h := checkLog_sound (w := (24443 / 75643)) (n := 12)
    (lo := (167572571 / 250000000)) (hi := (134058057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50043 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50043 / 25600) = 1/(25600 / 50043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167572571 / 250000000) (134058057 / 200000000) (Real.log (50043 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50043 / 25600) = -Real.log (25600 / 50043) := by
    rw [show ((50043 / 25600) : ℝ) = ((25600 / 50043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3096761901 / 1000000000) ≤ -Real.log (1157 / 25600) ∧
    -Real.log (1157 / 25600) ≤ (1548380953 / 500000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1157) = 1/(1157 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1548380953 / 500000000) (-3096761901 / 1000000000) (Real.log (1157 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341768071 / 500000000) ≤ -Real.log (100000 / 198087) ∧
    -Real.log (100000 / 198087) ≤ (683536143 / 1000000000) := by
  have h := checkLog_sound (w := (98087 / 298087)) (n := 12)
    (lo := (341768071 / 500000000)) (hi := (683536143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198087 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198087 / 100000) = 1/(100000 / 198087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341768071 / 500000000) (683536143 / 1000000000) (Real.log (198087 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (198087 / 100000) = -Real.log (100000 / 198087) := by
    rw [show ((198087 / 100000) : ℝ) = ((100000 / 198087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (989124373 / 250000000) ≤ -Real.log (1913 / 100000) ∧
    -Real.log (1913 / 100000) ≤ (1978248749 / 500000000) := by
  have h := checkLog_sound (w := (606 / 2519)) (n := 12)
    (lo := (61345199 / 125000000)) (hi := (490761593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1913) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1913) = 1/(1913 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1978248749 / 500000000) (-989124373 / 250000000) (Real.log (1913 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683612873 / 1000000000) ≤ -Real.log (500000 / 990511) ∧
    -Real.log (500000 / 990511) ≤ (341806437 / 500000000) := by
  have h := checkLog_sound (w := (490511 / 1490511)) (n := 12)
    (lo := (683612873 / 1000000000)) (hi := (341806437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990511 / 500000) = 1/(500000 / 990511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683612873 / 1000000000) (341806437 / 500000000) (Real.log (990511 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (990511 / 500000) = -Real.log (500000 / 990511) := by
    rw [show ((990511 / 500000) : ℝ) = ((500000 / 990511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1982237431 / 500000000) ≤ -Real.log (9489 / 500000) ∧
    -Real.log (9489 / 500000) ≤ (991118717 / 250000000) := by
  have h := checkLog_sound (w := (3068 / 12557)) (n := 12)
    (lo := (249369481 / 500000000)) (hi := (498738963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9489) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9489) = 1/(9489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-991118717 / 250000000) (-1982237431 / 500000000) (Real.log (9489 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2733981 / 4000000) ≤ -Real.log (1000000 / 1980789) ∧
    -Real.log (1000000 / 1980789) ≤ (683495251 / 1000000000) := by
  have h := checkLog_sound (w := (980789 / 2980789)) (n := 12)
    (lo := (2733981 / 4000000)) (hi := (683495251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980789 / 1000000) = 1/(1000000 / 1980789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2733981 / 4000000) (683495251 / 1000000000) (Real.log (1980789 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980789 / 1000000) = -Real.log (1000000 / 1980789) := by
    rw [show ((1980789 / 1000000) : ℝ) = ((1000000 / 1980789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (988068061 / 250000000) ≤ -Real.log (19211 / 1000000) ∧
    -Real.log (19211 / 1000000) ≤ (15809089 / 4000000) := by
  have h := checkLog_sound (w := (12039 / 50461)) (n := 12)
    (lo := (60817043 / 125000000)) (hi := (97307269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19211) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19211) = 1/(19211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15809089 / 4000000) (-988068061 / 250000000) (Real.log (19211 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683572993 / 1000000000) ≤ -Real.log (1000000 / 1980943) ∧
    -Real.log (1000000 / 1980943) ≤ (341786497 / 500000000) := by
  have h := checkLog_sound (w := (980943 / 2980943)) (n := 12)
    (lo := (683572993 / 1000000000)) (hi := (341786497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980943 / 1000000) = 1/(1000000 / 1980943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683572993 / 1000000000) (341786497 / 500000000) (Real.log (1980943 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1980943 / 1000000) = -Real.log (1000000 / 1980943) := by
    rw [show ((1980943 / 1000000) : ℝ) = ((1000000 / 1980943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (990080197 / 250000000) ≤ -Real.log (19057 / 1000000) ∧
    -Real.log (19057 / 1000000) ≤ (1980160397 / 500000000) := by
  have h := checkLog_sound (w := (12193 / 50307)) (n := 12)
    (lo := (61823111 / 125000000)) (hi := (494584889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19057) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19057) = 1/(19057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1980160397 / 500000000) (-990080197 / 250000000) (Real.log (19057 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2320016817 / 500000000) ≤ -Real.log (500000000000 / 51773915316257) ∧
    -Real.log (500000000000 / 51773915316257) ≤ (4640033641 / 1000000000) := by
  have h := checkLog_sound (w := (19773915316257 / 83773915316257)) (n := 12)
    (lo := (240575277 / 500000000)) (hi := (96230111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51773915316257 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51773915316257 / 32000000000000) = 1/(500000000000 / 51773915316257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2320016817 / 500000000) (4640033641 / 1000000000) (Real.log (51773915316257 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (51773915316257 / 500000000000) = -Real.log (500000000000 / 51773915316257) := by
    rw [show ((51773915316257 / 500000000000) : ℝ) = ((500000000000 / 51773915316257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (929617547 / 200000000) ≤ -Real.log (500000000000 / 52192591421647) ∧
    -Real.log (500000000000 / 52192591421647) ≤ (2324043871 / 500000000) := by
  have h := checkLog_sound (w := (20192591421647 / 84192591421647)) (n := 12)
    (lo := (97840931 / 200000000)) (hi := (30575291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52192591421647 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52192591421647 / 32000000000000) = 1/(500000000000 / 52192591421647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (929617547 / 200000000) (2324043871 / 500000000) (Real.log (52192591421647 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (52192591421647 / 500000000000) = -Real.log (500000000000 / 52192591421647) := by
    rw [show ((52192591421647 / 500000000000) : ℝ) = ((500000000000 / 52192591421647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2317883747 / 500000000) ≤ -Real.log (500000000000 / 51553511009317) ∧
    -Real.log (500000000000 / 51553511009317) ≤ (4635767501 / 1000000000) := by
  have h := checkLog_sound (w := (19553511009317 / 83553511009317)) (n := 12)
    (lo := (238442207 / 500000000)) (hi := (95376883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51553511009317 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51553511009317 / 32000000000000) = 1/(500000000000 / 51553511009317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2317883747 / 500000000) (4635767501 / 1000000000) (Real.log (51553511009317 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (51553511009317 / 500000000000) = -Real.log (500000000000 / 51553511009317) := by
    rw [show ((51553511009317 / 500000000000) : ℝ) = ((500000000000 / 51553511009317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4643893781 / 1000000000) ≤ -Real.log (100000000000 / 10394831295587) ∧
    -Real.log (100000000000 / 10394831295587) ≤ (1160973447 / 250000000) := by
  have h := checkLog_sound (w := (3994831295587 / 16794831295587)) (n := 12)
    (lo := (485010701 / 1000000000)) (hi := (242505351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10394831295587 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10394831295587 / 6400000000000) = 1/(100000000000 / 10394831295587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4643893781 / 1000000000) (1160973447 / 250000000) (Real.log (10394831295587 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10394831295587 / 100000000000) = -Real.log (100000000000 / 10394831295587) := by
    rw [show ((10394831295587 / 100000000000) : ℝ) = ((100000000000 / 10394831295587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0020

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0021Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0021
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

theorem reflection_log_1_neg : (136356807 / 200000000) ≤ -Real.log (51200 / 101243) ∧
    -Real.log (51200 / 101243) ≤ (170446009 / 250000000) := by
  have h := checkLog_sound (w := (50043 / 152443)) (n := 12)
    (lo := (136356807 / 200000000)) (hi := (170446009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101243 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101243 / 51200) = 1/(51200 / 101243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136356807 / 200000000) (170446009 / 250000000) (Real.log (101243 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101243 / 51200) = -Real.log (51200 / 101243) := by
    rw [show ((101243 / 51200) : ℝ) = ((51200 / 101243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3789909081 / 1000000000) ≤ -Real.log (1157 / 51200) ∧
    -Real.log (1157 / 51200) ≤ (3789909087 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1157) = 1/(1157 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3789909087 / 1000000000) (-3789909081 / 1000000000) (Real.log (1157 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (681690197 / 1000000000) ≤ -Real.log (102400 / 202467) ∧
    -Real.log (102400 / 202467) ≤ (340845099 / 500000000) := by
  have h := checkLog_sound (w := (100067 / 304867)) (n := 12)
    (lo := (681690197 / 1000000000)) (hi := (340845099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202467 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202467 / 102400) = 1/(102400 / 202467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (681690197 / 1000000000) (340845099 / 500000000) (Real.log (202467 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202467 / 102400) = -Real.log (102400 / 202467) := by
    rw [show ((202467 / 102400) : ℝ) = ((102400 / 202467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (945432929 / 250000000) ≤ -Real.log (2333 / 102400) ∧
    -Real.log (2333 / 102400) ≤ (1890865861 / 500000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2333) = 1/(2333 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1890865861 / 500000000) (-945432929 / 250000000) (Real.log (2333 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167572571 / 250000000) ≤ -Real.log (25600 / 50043) ∧
    -Real.log (25600 / 50043) ≤ (134058057 / 200000000) := by
  have h := checkLog_sound (w := (24443 / 75643)) (n := 12)
    (lo := (167572571 / 250000000)) (hi := (134058057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50043 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50043 / 25600) = 1/(25600 / 50043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167572571 / 250000000) (134058057 / 200000000) (Real.log (50043 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50043 / 25600) = -Real.log (25600 / 50043) := by
    rw [show ((50043 / 25600) : ℝ) = ((25600 / 50043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3096761901 / 1000000000) ≤ -Real.log (1157 / 25600) ∧
    -Real.log (1157 / 25600) ≤ (1548380953 / 500000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1157) = 1/(1157 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1548380953 / 500000000) (-3096761901 / 1000000000) (Real.log (1157 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (670100429 / 1000000000) ≤ -Real.log (51200 / 100067) ∧
    -Real.log (51200 / 100067) ≤ (67010043 / 100000000) := by
  have h := checkLog_sound (w := (48867 / 151267)) (n := 12)
    (lo := (670100429 / 1000000000)) (hi := (67010043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100067 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100067 / 51200) = 1/(51200 / 100067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (670100429 / 1000000000) (67010043 / 100000000) (Real.log (100067 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100067 / 51200) = -Real.log (51200 / 100067) := by
    rw [show ((100067 / 51200) : ℝ) = ((51200 / 100067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (386073067 / 125000000) ≤ -Real.log (2333 / 51200) ∧
    -Real.log (2333 / 51200) ≤ (3088584541 / 1000000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2333) = 1/(2333 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3088584541 / 1000000000) (-386073067 / 125000000) (Real.log (2333 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68345991 / 100000000) ≤ -Real.log (1000000 / 1980719) ∧
    -Real.log (1000000 / 1980719) ≤ (683459911 / 1000000000) := by
  have h := checkLog_sound (w := (980719 / 2980719)) (n := 12)
    (lo := (68345991 / 100000000)) (hi := (683459911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980719 / 1000000) = 1/(1000000 / 1980719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68345991 / 100000000) (683459911 / 1000000000) (Real.log (1980719 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1980719 / 1000000) = -Real.log (1000000 / 1980719) := by
    rw [show ((1980719 / 1000000) : ℝ) = ((1000000 / 1980719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3948635121 / 1000000000) ≤ -Real.log (19281 / 1000000) ∧
    -Real.log (19281 / 1000000) ≤ (3948635127 / 1000000000) := by
  have h := checkLog_sound (w := (11969 / 50531)) (n := 12)
    (lo := (482899221 / 1000000000)) (hi := (241449611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19281) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19281) = 1/(19281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3948635127 / 1000000000) (-3948635121 / 1000000000) (Real.log (19281 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341768323 / 500000000) ≤ -Real.log (1000000 / 1980871) ∧
    -Real.log (1000000 / 1980871) ≤ (683536647 / 1000000000) := by
  have h := checkLog_sound (w := (980871 / 2980871)) (n := 12)
    (lo := (341768323 / 500000000)) (hi := (683536647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980871 / 1000000) = 1/(1000000 / 1980871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341768323 / 500000000) (683536647 / 1000000000) (Real.log (1980871 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980871 / 1000000) = -Real.log (1000000 / 1980871) := by
    rw [show ((1980871 / 1000000) : ℝ) = ((1000000 / 1980871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (494568721 / 125000000) ≤ -Real.log (19129 / 1000000) ∧
    -Real.log (19129 / 1000000) ≤ (1978274887 / 500000000) := by
  have h := checkLog_sound (w := (12121 / 50379)) (n := 12)
    (lo := (122703467 / 250000000)) (hi := (490813869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19129) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19129) = 1/(19129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1978274887 / 500000000) (-494568721 / 125000000) (Real.log (19129 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68341851 / 100000000) ≤ -Real.log (1000000 / 1980637) ∧
    -Real.log (1000000 / 1980637) ≤ (683418511 / 1000000000) := by
  have h := checkLog_sound (w := (980637 / 2980637)) (n := 12)
    (lo := (68341851 / 100000000)) (hi := (683418511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980637 / 1000000) = 1/(1000000 / 1980637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68341851 / 100000000) (683418511 / 1000000000) (Real.log (1980637 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980637 / 1000000) = -Real.log (1000000 / 1980637) := by
    rw [show ((1980637 / 1000000) : ℝ) = ((1000000 / 1980637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3944391247 / 1000000000) ≤ -Real.log (19363 / 1000000) ∧
    -Real.log (19363 / 1000000) ≤ (3944391253 / 1000000000) := by
  have h := checkLog_sound (w := (11887 / 50613)) (n := 12)
    (lo := (478655347 / 1000000000)) (hi := (119663837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19363) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19363) = 1/(19363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3944391253 / 1000000000) (-3944391247 / 1000000000) (Real.log (19363 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136699151 / 200000000) ≤ -Real.log (100000 / 198079) ∧
    -Real.log (100000 / 198079) ≤ (170873939 / 250000000) := by
  have h := checkLog_sound (w := (98079 / 298079)) (n := 12)
    (lo := (136699151 / 200000000)) (hi := (170873939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198079 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198079 / 100000) = 1/(100000 / 198079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136699151 / 200000000) (170873939 / 250000000) (Real.log (198079 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (198079 / 100000) = -Real.log (100000 / 198079) := by
    rw [show ((198079 / 100000) : ℝ) = ((100000 / 198079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3952324299 / 1000000000) ≤ -Real.log (1921 / 100000) ∧
    -Real.log (1921 / 100000) ≤ (790464861 / 200000000) := by
  have h := checkLog_sound (w := (602 / 2523)) (n := 12)
    (lo := (486588399 / 1000000000)) (hi := (1216471 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1921) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1921) = 1/(1921 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-790464861 / 200000000) (-3952324299 / 1000000000) (Real.log (1921 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (463209503 / 100000000) ≤ -Real.log (125000000000 / 12841132462009) ∧
    -Real.log (125000000000 / 12841132462009) ≤ (4632095037 / 1000000000) := by
  have h := checkLog_sound (w := (4841132462009 / 20841132462009)) (n := 12)
    (lo := (9464239 / 20000000)) (hi := (473211951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12841132462009 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12841132462009 / 8000000000000) = 1/(125000000000 / 12841132462009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (463209503 / 100000000) (4632095037 / 1000000000) (Real.log (12841132462009 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12841132462009 / 125000000000) = -Real.log (125000000000 / 12841132462009) := by
    rw [show ((12841132462009 / 125000000000) : ℝ) = ((125000000000 / 12841132462009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2320043207 / 500000000) ≤ -Real.log (500000000000 / 51776648021329) ∧
    -Real.log (500000000000 / 51776648021329) ≤ (4640086421 / 1000000000) := by
  have h := checkLog_sound (w := (19776648021329 / 83776648021329)) (n := 12)
    (lo := (240601667 / 500000000)) (hi := (96240667 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51776648021329 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51776648021329 / 32000000000000) = 1/(500000000000 / 51776648021329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2320043207 / 500000000) (4640086421 / 1000000000) (Real.log (51776648021329 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51776648021329 / 500000000000) = -Real.log (500000000000 / 51776648021329) := by
    rw [show ((51776648021329 / 500000000000) : ℝ) = ((500000000000 / 51776648021329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4627809757 / 1000000000) ≤ -Real.log (6250000000 / 639311121727) ∧
    -Real.log (6250000000 / 639311121727) ≤ (1156952441 / 250000000) := by
  have h := checkLog_sound (w := (239311121727 / 1039311121727)) (n := 12)
    (lo := (468926677 / 1000000000)) (hi := (234463339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639311121727 / 400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(639311121727 / 400000000000) = 1/(6250000000 / 639311121727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4627809757 / 1000000000) (1156952441 / 250000000) (Real.log (639311121727 / 6250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (639311121727 / 6250000000) = -Real.log (6250000000 / 639311121727) := by
    rw [show ((639311121727 / 6250000000) : ℝ) = ((6250000000 / 639311121727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4635820053 / 1000000000) ≤ -Real.log (62500000000 / 6444527589797) ∧
    -Real.log (62500000000 / 6444527589797) ≤ (231791003 / 50000000) := by
  have h := checkLog_sound (w := (2444527589797 / 10444527589797)) (n := 12)
    (lo := (476936973 / 1000000000)) (hi := (238468487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6444527589797 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6444527589797 / 4000000000000) = 1/(62500000000 / 6444527589797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4635820053 / 1000000000) (231791003 / 50000000) (Real.log (6444527589797 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6444527589797 / 62500000000) = -Real.log (62500000000 / 6444527589797) := by
    rw [show ((6444527589797 / 62500000000) : ℝ) = ((62500000000 / 6444527589797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0021

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0022Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0022
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

theorem reflection_log_1_neg : (681690197 / 1000000000) ≤ -Real.log (102400 / 202467) ∧
    -Real.log (102400 / 202467) ≤ (340845099 / 500000000) := by
  have h := checkLog_sound (w := (100067 / 304867)) (n := 12)
    (lo := (681690197 / 1000000000)) (hi := (340845099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202467 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202467 / 102400) = 1/(102400 / 202467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (681690197 / 1000000000) (340845099 / 500000000) (Real.log (202467 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202467 / 102400) = -Real.log (102400 / 202467) := by
    rw [show ((202467 / 102400) : ℝ) = ((102400 / 202467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (945432929 / 250000000) ≤ -Real.log (2333 / 102400) ∧
    -Real.log (2333 / 102400) ≤ (1890865861 / 500000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2333) = 1/(2333 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1890865861 / 500000000) (-945432929 / 250000000) (Real.log (2333 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13631927 / 20000000) ≤ -Real.log (6400 / 12653) ∧
    -Real.log (6400 / 12653) ≤ (681596351 / 1000000000) := by
  have h := checkLog_sound (w := (6253 / 19053)) (n := 12)
    (lo := (13631927 / 20000000)) (hi := (681596351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12653 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12653 / 6400) = 1/(6400 / 12653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13631927 / 20000000) (681596351 / 1000000000) (Real.log (12653 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12653 / 6400) = -Real.log (6400 / 12653) := by
    rw [show ((12653 / 6400) : ℝ) = ((6400 / 12653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3773620679 / 1000000000) ≤ -Real.log (147 / 6400) ∧
    -Real.log (147 / 6400) ≤ (754724137 / 200000000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(200 / 147) = 1/(147 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-754724137 / 200000000) (-3773620679 / 1000000000) (Real.log (147 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (670100429 / 1000000000) ≤ -Real.log (51200 / 100067) ∧
    -Real.log (51200 / 100067) ≤ (67010043 / 100000000) := by
  have h := checkLog_sound (w := (48867 / 151267)) (n := 12)
    (lo := (670100429 / 1000000000)) (hi := (67010043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100067 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100067 / 51200) = 1/(51200 / 100067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (670100429 / 1000000000) (67010043 / 100000000) (Real.log (100067 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100067 / 51200) = -Real.log (51200 / 100067) := by
    rw [show ((100067 / 51200) : ℝ) = ((51200 / 100067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (386073067 / 125000000) ≤ -Real.log (2333 / 51200) ∧
    -Real.log (2333 / 51200) ≤ (3088584541 / 1000000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2333) = 1/(2333 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3088584541 / 1000000000) (-386073067 / 125000000) (Real.log (2333 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (334955269 / 500000000) ≤ -Real.log (3200 / 6253) ∧
    -Real.log (3200 / 6253) ≤ (669910539 / 1000000000) := by
  have h := checkLog_sound (w := (3053 / 9453)) (n := 12)
    (lo := (334955269 / 500000000)) (hi := (669910539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6253 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6253 / 3200) = 1/(3200 / 6253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (334955269 / 500000000) (669910539 / 1000000000) (Real.log (6253 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6253 / 3200) = -Real.log (3200 / 6253) := by
    rw [show ((6253 / 3200) : ℝ) = ((3200 / 6253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3080473499 / 1000000000) ≤ -Real.log (147 / 3200) ∧
    -Real.log (147 / 3200) ≤ (96264797 / 31250000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 147) = 1/(147 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-96264797 / 31250000) (-3080473499 / 1000000000) (Real.log (147 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683384177 / 1000000000) ≤ -Real.log (1000000 / 1980569) ∧
    -Real.log (1000000 / 1980569) ≤ (341692089 / 500000000) := by
  have h := checkLog_sound (w := (980569 / 2980569)) (n := 12)
    (lo := (683384177 / 1000000000)) (hi := (341692089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980569 / 1000000) = 1/(1000000 / 1980569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683384177 / 1000000000) (341692089 / 500000000) (Real.log (1980569 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1980569 / 1000000) = -Real.log (1000000 / 1980569) := by
    rw [show ((1980569 / 1000000) : ℝ) = ((1000000 / 1980569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3940885547 / 1000000000) ≤ -Real.log (19431 / 1000000) ∧
    -Real.log (19431 / 1000000) ≤ (3940885553 / 1000000000) := by
  have h := checkLog_sound (w := (11819 / 50681)) (n := 12)
    (lo := (475149647 / 1000000000)) (hi := (29696853 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19431) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19431) = 1/(19431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3940885553 / 1000000000) (-3940885547 / 1000000000) (Real.log (19431 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341730207 / 500000000) ≤ -Real.log (12500 / 24759) ∧
    -Real.log (12500 / 24759) ≤ (136692083 / 200000000) := by
  have h := checkLog_sound (w := (12259 / 37259)) (n := 12)
    (lo := (341730207 / 500000000)) (hi := (136692083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24759 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24759 / 12500) = 1/(12500 / 24759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341730207 / 500000000) (136692083 / 200000000) (Real.log (24759 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (24759 / 12500) = -Real.log (12500 / 24759) := by
    rw [show ((24759 / 12500) : ℝ) = ((12500 / 24759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3948686987 / 1000000000) ≤ -Real.log (241 / 12500) ∧
    -Real.log (241 / 12500) ≤ (3948686993 / 1000000000) := by
  have h := checkLog_sound (w := (1197 / 5053)) (n := 12)
    (lo := (482951087 / 1000000000)) (hi := (30184443 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1928) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1928) = 1/(241 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3948686993 / 1000000000) (-3948686987 / 1000000000) (Real.log (241 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170835441 / 250000000) ≤ -Real.log (200000 / 396097) ∧
    -Real.log (200000 / 396097) ≤ (136668353 / 200000000) := by
  have h := checkLog_sound (w := (196097 / 596097)) (n := 12)
    (lo := (170835441 / 250000000)) (hi := (136668353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396097 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396097 / 200000) = 1/(200000 / 396097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170835441 / 250000000) (136668353 / 200000000) (Real.log (396097 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (396097 / 200000) = -Real.log (200000 / 396097) := by
    rw [show ((396097 / 200000) : ℝ) = ((200000 / 396097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1259703 / 320000) ≤ -Real.log (3903 / 200000) ∧
    -Real.log (3903 / 200000) ≤ (3936571881 / 1000000000) := by
  have h := checkLog_sound (w := (2347 / 10153)) (n := 12)
    (lo := (18833439 / 40000000)) (hi := (58854497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3903) = 1/(3903 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3936571881 / 1000000000) (-1259703 / 320000) (Real.log (3903 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136683803 / 200000000) ≤ -Real.log (500000 / 990319) ∧
    -Real.log (500000 / 990319) ≤ (85427377 / 125000000) := by
  have h := checkLog_sound (w := (490319 / 1490319)) (n := 12)
    (lo := (136683803 / 200000000)) (hi := (85427377 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990319 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990319 / 500000) = 1/(500000 / 990319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136683803 / 200000000) (85427377 / 125000000) (Real.log (990319 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990319 / 500000) = -Real.log (500000 / 990319) := by
    rw [show ((990319 / 500000) : ℝ) = ((500000 / 990319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3944442893 / 1000000000) ≤ -Real.log (9681 / 500000) ∧
    -Real.log (9681 / 500000) ≤ (3944442899 / 1000000000) := by
  have h := checkLog_sound (w := (2972 / 12653)) (n := 12)
    (lo := (478706993 / 1000000000)) (hi := (239353497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9681) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9681) = 1/(9681 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3944442899 / 1000000000) (-3944442893 / 1000000000) (Real.log (9681 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4624269723 / 1000000000) ≤ -Real.log (125000000000 / 12741038803973) ∧
    -Real.log (125000000000 / 12741038803973) ≤ (462426973 / 100000000) := by
  have h := checkLog_sound (w := (4741038803973 / 20741038803973)) (n := 12)
    (lo := (465386643 / 1000000000)) (hi := (116346661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12741038803973 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12741038803973 / 8000000000000) = 1/(125000000000 / 12741038803973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4624269723 / 1000000000) (462426973 / 100000000) (Real.log (12741038803973 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12741038803973 / 125000000000) = -Real.log (125000000000 / 12741038803973) := by
    rw [show ((12741038803973 / 125000000000) : ℝ) = ((125000000000 / 12741038803973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4632147401 / 1000000000) ≤ -Real.log (500000000000 / 51367219917013) ∧
    -Real.log (500000000000 / 51367219917013) ≤ (289509213 / 62500000) := by
  have h := checkLog_sound (w := (19367219917013 / 83367219917013)) (n := 12)
    (lo := (473264321 / 1000000000)) (hi := (236632161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51367219917013 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51367219917013 / 32000000000000) = 1/(500000000000 / 51367219917013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4632147401 / 1000000000) (289509213 / 62500000) (Real.log (51367219917013 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51367219917013 / 500000000000) = -Real.log (500000000000 / 51367219917013) := by
    rw [show ((51367219917013 / 500000000000) : ℝ) = ((500000000000 / 51367219917013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4619913639 / 1000000000) ≤ -Real.log (25000000000 / 2537131693569) ∧
    -Real.log (25000000000 / 2537131693569) ≤ (2309956823 / 500000000) := by
  have h := checkLog_sound (w := (937131693569 / 4137131693569)) (n := 12)
    (lo := (461030559 / 1000000000)) (hi := (2881441 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2537131693569 / 1600000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2537131693569 / 1600000000000) = 1/(25000000000 / 2537131693569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4619913639 / 1000000000) (2309956823 / 500000000) (Real.log (2537131693569 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2537131693569 / 25000000000) = -Real.log (25000000000 / 2537131693569) := by
    rw [show ((2537131693569 / 25000000000) : ℝ) = ((25000000000 / 2537131693569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1156965477 / 250000000) ≤ -Real.log (500000000000 / 51147557070551) ∧
    -Real.log (500000000000 / 51147557070551) ≤ (925572383 / 200000000) := by
  have h := checkLog_sound (w := (19147557070551 / 83147557070551)) (n := 12)
    (lo := (117244707 / 250000000)) (hi := (468978829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51147557070551 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51147557070551 / 32000000000000) = 1/(500000000000 / 51147557070551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1156965477 / 250000000) (925572383 / 200000000) (Real.log (51147557070551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (51147557070551 / 500000000000) = -Real.log (500000000000 / 51147557070551) := by
    rw [show ((51147557070551 / 500000000000) : ℝ) = ((500000000000 / 51147557070551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0022

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0023Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0023
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

theorem reflection_log_1_neg : (13631927 / 20000000) ≤ -Real.log (6400 / 12653) ∧
    -Real.log (6400 / 12653) ≤ (681596351 / 1000000000) := by
  have h := checkLog_sound (w := (6253 / 19053)) (n := 12)
    (lo := (13631927 / 20000000)) (hi := (681596351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12653 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12653 / 6400) = 1/(6400 / 12653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13631927 / 20000000) (681596351 / 1000000000) (Real.log (12653 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12653 / 6400) = -Real.log (6400 / 12653) := by
    rw [show ((12653 / 6400) : ℝ) = ((6400 / 12653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3773620679 / 1000000000) ≤ -Real.log (147 / 6400) ∧
    -Real.log (147 / 6400) ≤ (754724137 / 200000000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(200 / 147) = 1/(147 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-754724137 / 200000000) (-3773620679 / 1000000000) (Real.log (147 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136300499 / 200000000) ≤ -Real.log (102400 / 202429) ∧
    -Real.log (102400 / 202429) ≤ (21296953 / 31250000) := by
  have h := checkLog_sound (w := (100029 / 304829)) (n := 12)
    (lo := (136300499 / 200000000)) (hi := (21296953 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202429 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202429 / 102400) = 1/(102400 / 202429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136300499 / 200000000) (21296953 / 31250000) (Real.log (202429 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202429 / 102400) = -Real.log (102400 / 202429) := by
    rw [show ((202429 / 102400) : ℝ) = ((102400 / 202429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1882787451 / 500000000) ≤ -Real.log (2371 / 102400) ∧
    -Real.log (2371 / 102400) ≤ (941393727 / 250000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2371) = 1/(2371 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-941393727 / 250000000) (-1882787451 / 500000000) (Real.log (2371 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (334955269 / 500000000) ≤ -Real.log (3200 / 6253) ∧
    -Real.log (3200 / 6253) ≤ (669910539 / 1000000000) := by
  have h := checkLog_sound (w := (3053 / 9453)) (n := 12)
    (lo := (334955269 / 500000000)) (hi := (669910539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6253 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6253 / 3200) = 1/(3200 / 6253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (334955269 / 500000000) (669910539 / 1000000000) (Real.log (6253 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6253 / 3200) = -Real.log (3200 / 6253) := by
    rw [show ((6253 / 3200) : ℝ) = ((3200 / 6253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3080473499 / 1000000000) ≤ -Real.log (147 / 3200) ∧
    -Real.log (147 / 3200) ≤ (96264797 / 31250000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 147) = 1/(147 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-96264797 / 31250000) (-3080473499 / 1000000000) (Real.log (147 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (669720611 / 1000000000) ≤ -Real.log (51200 / 100029) ∧
    -Real.log (51200 / 100029) ≤ (167430153 / 250000000) := by
  have h := checkLog_sound (w := (48829 / 151229)) (n := 12)
    (lo := (669720611 / 1000000000)) (hi := (167430153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100029 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100029 / 51200) = 1/(51200 / 100029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (669720611 / 1000000000) (167430153 / 250000000) (Real.log (100029 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100029 / 51200) = -Real.log (51200 / 100029) := by
    rw [show ((100029 / 51200) : ℝ) = ((51200 / 100029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1536213861 / 500000000) ≤ -Real.log (2371 / 51200) ∧
    -Real.log (2371 / 51200) ≤ (3072427727 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2371) = 1/(2371 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3072427727 / 1000000000) (-1536213861 / 500000000) (Real.log (2371 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683307933 / 1000000000) ≤ -Real.log (500000 / 990209) ∧
    -Real.log (500000 / 990209) ≤ (341653967 / 500000000) := by
  have h := checkLog_sound (w := (490209 / 1490209)) (n := 12)
    (lo := (683307933 / 1000000000)) (hi := (341653967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990209 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990209 / 500000) = 1/(500000 / 990209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683307933 / 1000000000) (341653967 / 500000000) (Real.log (990209 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990209 / 500000) = -Real.log (500000 / 990209) := by
    rw [show ((990209 / 500000) : ℝ) = ((500000 / 990209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3933144499 / 1000000000) ≤ -Real.log (9791 / 500000) ∧
    -Real.log (9791 / 500000) ≤ (786628901 / 200000000) := by
  have h := checkLog_sound (w := (2917 / 12708)) (n := 12)
    (lo := (467408599 / 1000000000)) (hi := (2337043 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9791) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9791) = 1/(9791 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-786628901 / 200000000) (-3933144499 / 1000000000) (Real.log (9791 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341692341 / 500000000) ≤ -Real.log (100000 / 198057) ∧
    -Real.log (100000 / 198057) ≤ (683384683 / 1000000000) := by
  have h := checkLog_sound (w := (98057 / 298057)) (n := 12)
    (lo := (341692341 / 500000000)) (hi := (683384683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198057 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198057 / 100000) = 1/(100000 / 198057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341692341 / 500000000) (683384683 / 1000000000) (Real.log (198057 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (198057 / 100000) = -Real.log (100000 / 198057) := by
    rw [show ((198057 / 100000) : ℝ) = ((100000 / 198057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (985234253 / 250000000) ≤ -Real.log (1943 / 100000) ∧
    -Real.log (1943 / 100000) ≤ (1970468509 / 500000000) := by
  have h := checkLog_sound (w := (591 / 2534)) (n := 12)
    (lo := (59400139 / 125000000)) (hi := (475201113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1943) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1943) = 1/(1943 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1970468509 / 500000000) (-985234253 / 250000000) (Real.log (1943 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170816253 / 250000000) ≤ -Real.log (1000000 / 1980333) ∧
    -Real.log (1000000 / 1980333) ≤ (683265013 / 1000000000) := by
  have h := checkLog_sound (w := (980333 / 2980333)) (n := 12)
    (lo := (170816253 / 250000000)) (hi := (683265013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980333 / 1000000) = 1/(1000000 / 1980333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170816253 / 250000000) (683265013 / 1000000000) (Real.log (1980333 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980333 / 1000000) = -Real.log (1000000 / 1980333) := by
    rw [show ((1980333 / 1000000) : ℝ) = ((1000000 / 1980333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3928813171 / 1000000000) ≤ -Real.log (19667 / 1000000) ∧
    -Real.log (19667 / 1000000) ≤ (3928813177 / 1000000000) := by
  have h := checkLog_sound (w := (11583 / 50917)) (n := 12)
    (lo := (463077271 / 1000000000)) (hi := (57884659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19667) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19667) = 1/(19667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3928813177 / 1000000000) (-3928813171 / 1000000000) (Real.log (19667 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683342269 / 1000000000) ≤ -Real.log (500000 / 990243) ∧
    -Real.log (500000 / 990243) ≤ (68334227 / 100000000) := by
  have h := checkLog_sound (w := (490243 / 1490243)) (n := 12)
    (lo := (683342269 / 1000000000)) (hi := (68334227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990243 / 500000) = 1/(500000 / 990243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683342269 / 1000000000) (68334227 / 100000000) (Real.log (990243 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990243 / 500000) = -Real.log (500000 / 990243) := by
    rw [show ((990243 / 500000) : ℝ) = ((500000 / 990243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3936623119 / 1000000000) ≤ -Real.log (9757 / 500000) ∧
    -Real.log (9757 / 500000) ≤ (6298597 / 1600000) := by
  have h := checkLog_sound (w := (2934 / 12691)) (n := 12)
    (lo := (470887219 / 1000000000)) (hi := (23544361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9757) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9757) = 1/(9757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-6298597 / 1600000) (-3936623119 / 1000000000) (Real.log (9757 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (288528277 / 62500000) ≤ -Real.log (125000000000 / 12641826677561) ∧
    -Real.log (125000000000 / 12641826677561) ≤ (4616452439 / 1000000000) := by
  have h := checkLog_sound (w := (4641826677561 / 20641826677561)) (n := 12)
    (lo := (57196169 / 125000000)) (hi := (457569353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12641826677561 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12641826677561 / 8000000000000) = 1/(125000000000 / 12641826677561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (288528277 / 62500000) (4616452439 / 1000000000) (Real.log (12641826677561 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12641826677561 / 125000000000) = -Real.log (125000000000 / 12641826677561) := by
    rw [show ((12641826677561 / 125000000000) : ℝ) = ((125000000000 / 12641826677561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2312160847 / 500000000) ≤ -Real.log (250000000000 / 25483401955739) ∧
    -Real.log (250000000000 / 25483401955739) ≤ (4624321701 / 1000000000) := by
  have h := checkLog_sound (w := (9483401955739 / 41483401955739)) (n := 12)
    (lo := (232719307 / 500000000)) (hi := (93087723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25483401955739 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25483401955739 / 16000000000000) = 1/(250000000000 / 25483401955739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2312160847 / 500000000) (4624321701 / 1000000000) (Real.log (25483401955739 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25483401955739 / 250000000000) = -Real.log (250000000000 / 25483401955739) := by
    rw [show ((25483401955739 / 250000000000) : ℝ) = ((250000000000 / 25483401955739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4612078183 / 1000000000) ≤ -Real.log (500000000000 / 50346595820409) ∧
    -Real.log (500000000000 / 50346595820409) ≤ (461207819 / 100000000) := by
  have h := checkLog_sound (w := (18346595820409 / 82346595820409)) (n := 12)
    (lo := (453195103 / 1000000000)) (hi := (14162347 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50346595820409 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(50346595820409 / 32000000000000) = 1/(500000000000 / 50346595820409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4612078183 / 1000000000) (461207819 / 100000000) (Real.log (50346595820409 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (50346595820409 / 500000000000) = -Real.log (500000000000 / 50346595820409) := by
    rw [show ((50346595820409 / 500000000000) : ℝ) = ((500000000000 / 50346595820409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1154991347 / 250000000) ≤ -Real.log (125000000000 / 12686314953367) ∧
    -Real.log (125000000000 / 12686314953367) ≤ (923993079 / 200000000) := by
  have h := checkLog_sound (w := (4686314953367 / 20686314953367)) (n := 12)
    (lo := (115270577 / 250000000)) (hi := (461082309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12686314953367 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12686314953367 / 8000000000000) = 1/(125000000000 / 12686314953367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1154991347 / 250000000) (923993079 / 200000000) (Real.log (12686314953367 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12686314953367 / 125000000000) = -Real.log (125000000000 / 12686314953367) := by
    rw [show ((12686314953367 / 125000000000) : ℝ) = ((125000000000 / 12686314953367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0023

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0024Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0024
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

theorem reflection_log_1_neg : (136300499 / 200000000) ≤ -Real.log (102400 / 202429) ∧
    -Real.log (102400 / 202429) ≤ (21296953 / 31250000) := by
  have h := checkLog_sound (w := (100029 / 304829)) (n := 12)
    (lo := (136300499 / 200000000)) (hi := (21296953 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202429 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202429 / 102400) = 1/(102400 / 202429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136300499 / 200000000) (21296953 / 31250000) (Real.log (202429 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202429 / 102400) = -Real.log (102400 / 202429) := by
    rw [show ((202429 / 102400) : ℝ) = ((102400 / 202429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1882787451 / 500000000) ≤ -Real.log (2371 / 102400) ∧
    -Real.log (2371 / 102400) ≤ (941393727 / 250000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2371) = 1/(2371 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-941393727 / 250000000) (-1882787451 / 500000000) (Real.log (2371 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (68140863 / 100000000) ≤ -Real.log (10240 / 20241) ∧
    -Real.log (10240 / 20241) ≤ (681408631 / 1000000000) := by
  have h := checkLog_sound (w := (10001 / 30481)) (n := 12)
    (lo := (68140863 / 100000000)) (hi := (681408631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20241 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20241 / 10240) = 1/(10240 / 20241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (68140863 / 100000000) (681408631 / 1000000000) (Real.log (20241 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20241 / 10240) = -Real.log (10240 / 20241) := by
    rw [show ((20241 / 10240) : ℝ) = ((10240 / 20241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3757593343 / 1000000000) ≤ -Real.log (239 / 10240) ∧
    -Real.log (239 / 10240) ≤ (3757593349 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 239) = 1/(239 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3757593349 / 1000000000) (-3757593343 / 1000000000) (Real.log (239 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (669720611 / 1000000000) ≤ -Real.log (51200 / 100029) ∧
    -Real.log (51200 / 100029) ≤ (167430153 / 250000000) := by
  have h := checkLog_sound (w := (48829 / 151229)) (n := 12)
    (lo := (669720611 / 1000000000)) (hi := (167430153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100029 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100029 / 51200) = 1/(51200 / 100029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (669720611 / 1000000000) (167430153 / 250000000) (Real.log (100029 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100029 / 51200) = -Real.log (51200 / 100029) := by
    rw [show ((100029 / 51200) : ℝ) = ((51200 / 100029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1536213861 / 500000000) ≤ -Real.log (2371 / 51200) ∧
    -Real.log (2371 / 51200) ≤ (3072427727 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2371) = 1/(2371 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3072427727 / 1000000000) (-1536213861 / 500000000) (Real.log (2371 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83691331 / 125000000) ≤ -Real.log (5120 / 10001) ∧
    -Real.log (5120 / 10001) ≤ (669530649 / 1000000000) := by
  have h := checkLog_sound (w := (4881 / 15121)) (n := 12)
    (lo := (83691331 / 125000000)) (hi := (669530649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001 / 5120) = 1/(5120 / 10001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83691331 / 125000000) (669530649 / 1000000000) (Real.log (10001 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (10001 / 5120) = -Real.log (5120 / 10001) := by
    rw [show ((10001 / 5120) : ℝ) = ((5120 / 10001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3064446163 / 1000000000) ≤ -Real.log (239 / 5120) ∧
    -Real.log (239 / 5120) ≤ (383055771 / 125000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 239) = 1/(239 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-383055771 / 125000000) (-3064446163 / 1000000000) (Real.log (239 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683232189 / 1000000000) ≤ -Real.log (250000 / 495067) ∧
    -Real.log (250000 / 495067) ≤ (68323219 / 100000000) := by
  have h := checkLog_sound (w := (245067 / 745067)) (n := 12)
    (lo := (683232189 / 1000000000)) (hi := (68323219 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495067 / 250000) = 1/(250000 / 495067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683232189 / 1000000000) (68323219 / 100000000) (Real.log (495067 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (495067 / 250000) = -Real.log (250000 / 495067) := by
    rw [show ((495067 / 250000) : ℝ) = ((250000 / 495067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (490689199 / 125000000) ≤ -Real.log (4933 / 250000) ∧
    -Real.log (4933 / 250000) ≤ (1962756799 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 25491)) (n := 12)
    (lo := (114944423 / 250000000)) (hi := (459777693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9866) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9866) = 1/(4933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1962756799 / 500000000) (-490689199 / 125000000) (Real.log (4933 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341654219 / 500000000) ≤ -Real.log (1000000 / 1980419) ∧
    -Real.log (1000000 / 1980419) ≤ (683308439 / 1000000000) := by
  have h := checkLog_sound (w := (980419 / 2980419)) (n := 12)
    (lo := (341654219 / 500000000)) (hi := (683308439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980419 / 1000000) = 1/(1000000 / 1980419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341654219 / 500000000) (683308439 / 1000000000) (Real.log (1980419 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980419 / 1000000) = -Real.log (1000000 / 1980419) := by
    rw [show ((1980419 / 1000000) : ℝ) = ((1000000 / 1980419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3933195567 / 1000000000) ≤ -Real.log (19581 / 1000000) ∧
    -Real.log (19581 / 1000000) ≤ (3933195573 / 1000000000) := by
  have h := checkLog_sound (w := (11669 / 50831)) (n := 12)
    (lo := (467459667 / 1000000000)) (hi := (116864917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19581) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19581) = 1/(19581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3933195573 / 1000000000) (-3933195567 / 1000000000) (Real.log (19581 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (341594127 / 500000000) ≤ -Real.log (1000000 / 1980181) ∧
    -Real.log (1000000 / 1980181) ≤ (136637651 / 200000000) := by
  have h := checkLog_sound (w := (980181 / 2980181)) (n := 12)
    (lo := (341594127 / 500000000)) (hi := (136637651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980181 / 1000000) = 1/(1000000 / 1980181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (341594127 / 500000000) (136637651 / 200000000) (Real.log (1980181 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980181 / 1000000) = -Real.log (1000000 / 1980181) := by
    rw [show ((1980181 / 1000000) : ℝ) = ((1000000 / 1980181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1960557101 / 500000000) ≤ -Real.log (19819 / 1000000) ∧
    -Real.log (19819 / 1000000) ≤ (122534819 / 31250000) := by
  have h := checkLog_sound (w := (11431 / 51069)) (n := 12)
    (lo := (227689151 / 500000000)) (hi := (455378303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19819) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19819) = 1/(19819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-122534819 / 31250000) (-1960557101 / 500000000) (Real.log (19819 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683265517 / 1000000000) ≤ -Real.log (500000 / 990167) ∧
    -Real.log (500000 / 990167) ≤ (341632759 / 500000000) := by
  have h := checkLog_sound (w := (490167 / 1490167)) (n := 12)
    (lo := (683265517 / 1000000000)) (hi := (341632759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990167 / 500000) = 1/(500000 / 990167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683265517 / 1000000000) (341632759 / 500000000) (Real.log (990167 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990167 / 500000) = -Real.log (500000 / 990167) := by
    rw [show ((990167 / 500000) : ℝ) = ((500000 / 990167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3928864019 / 1000000000) ≤ -Real.log (9833 / 500000) ∧
    -Real.log (9833 / 500000) ≤ (157154561 / 40000000) := by
  have h := checkLog_sound (w := (2896 / 12729)) (n := 12)
    (lo := (463128119 / 1000000000)) (hi := (11578203 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9833) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9833) = 1/(9833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-157154561 / 40000000) (-3928864019 / 1000000000) (Real.log (9833 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4608745781 / 1000000000) ≤ -Real.log (100000000000 / 10035819987837) ∧
    -Real.log (100000000000 / 10035819987837) ≤ (1152186447 / 250000000) := by
  have h := checkLog_sound (w := (3635819987837 / 16435819987837)) (n := 12)
    (lo := (449862701 / 1000000000)) (hi := (224931351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10035819987837 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10035819987837 / 6400000000000) = 1/(100000000000 / 10035819987837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4608745781 / 1000000000) (1152186447 / 250000000) (Real.log (10035819987837 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10035819987837 / 100000000000) = -Real.log (100000000000 / 10035819987837) := by
    rw [show ((10035819987837 / 100000000000) : ℝ) = ((100000000000 / 10035819987837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (923300801 / 200000000) ≤ -Real.log (500000000000 / 50569914713243) ∧
    -Real.log (500000000000 / 50569914713243) ≤ (1154126003 / 250000000) := by
  have h := checkLog_sound (w := (18569914713243 / 82569914713243)) (n := 12)
    (lo := (18304837 / 40000000)) (hi := (228810463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50569914713243 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(50569914713243 / 32000000000000) = 1/(500000000000 / 50569914713243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (923300801 / 200000000) (1154126003 / 250000000) (Real.log (50569914713243 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (50569914713243 / 500000000000) = -Real.log (500000000000 / 50569914713243) := by
    rw [show ((50569914713243 / 500000000000) : ℝ) = ((500000000000 / 50569914713243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (575537807 / 125000000) ≤ -Real.log (100000000000 / 9991326504869) ∧
    -Real.log (100000000000 / 9991326504869) ≤ (4604302463 / 1000000000) := by
  have h := checkLog_sound (w := (3591326504869 / 16391326504869)) (n := 12)
    (lo := (27838711 / 62500000)) (hi := (445419377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9991326504869 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9991326504869 / 6400000000000) = 1/(100000000000 / 9991326504869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (575537807 / 125000000) (4604302463 / 1000000000) (Real.log (9991326504869 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9991326504869 / 100000000000) = -Real.log (100000000000 / 9991326504869) := by
    rw [show ((9991326504869 / 100000000000) : ℝ) = ((100000000000 / 9991326504869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18016131 / 3906250) ≤ -Real.log (500000000000 / 50349181328181) ∧
    -Real.log (500000000000 / 50349181328181) ≤ (4612129543 / 1000000000) := by
  have h := checkLog_sound (w := (18349181328181 / 82349181328181)) (n := 12)
    (lo := (56655807 / 125000000)) (hi := (453246457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50349181328181 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(50349181328181 / 32000000000000) = 1/(500000000000 / 50349181328181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18016131 / 3906250) (4612129543 / 1000000000) (Real.log (50349181328181 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (50349181328181 / 500000000000) = -Real.log (500000000000 / 50349181328181) := by
    rw [show ((50349181328181 / 500000000000) : ℝ) = ((500000000000 / 50349181328181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0024

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0025Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0025
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

theorem reflection_log_1_neg : (68140863 / 100000000) ≤ -Real.log (10240 / 20241) ∧
    -Real.log (10240 / 20241) ≤ (681408631 / 1000000000) := by
  have h := checkLog_sound (w := (10001 / 30481)) (n := 12)
    (lo := (68140863 / 100000000)) (hi := (681408631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20241 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20241 / 10240) = 1/(10240 / 20241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (68140863 / 100000000) (681408631 / 1000000000) (Real.log (20241 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20241 / 10240) = -Real.log (10240 / 20241) := by
    rw [show ((20241 / 10240) : ℝ) = ((10240 / 20241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3757593343 / 1000000000) ≤ -Real.log (239 / 10240) ∧
    -Real.log (239 / 10240) ≤ (3757593349 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 239) = 1/(239 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3757593349 / 1000000000) (-3757593343 / 1000000000) (Real.log (239 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (681314757 / 1000000000) ≤ -Real.log (102400 / 202391) ∧
    -Real.log (102400 / 202391) ≤ (340657379 / 500000000) := by
  have h := checkLog_sound (w := (99991 / 304791)) (n := 12)
    (lo := (681314757 / 1000000000)) (hi := (340657379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202391 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202391 / 102400) = 1/(102400 / 202391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (681314757 / 1000000000) (340657379 / 500000000) (Real.log (202391 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202391 / 102400) = -Real.log (102400 / 202391) := by
    rw [show ((202391 / 102400) : ℝ) = ((102400 / 202391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1874837493 / 500000000) ≤ -Real.log (2409 / 102400) ∧
    -Real.log (2409 / 102400) ≤ (234354687 / 62500000) := by
  have h := checkLog_sound (w := (791 / 5609)) (n := 12)
    (lo := (141969543 / 500000000)) (hi := (283939087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2409) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2409) = 1/(2409 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-234354687 / 62500000) (-1874837493 / 500000000) (Real.log (2409 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (83691331 / 125000000) ≤ -Real.log (5120 / 10001) ∧
    -Real.log (5120 / 10001) ≤ (669530649 / 1000000000) := by
  have h := checkLog_sound (w := (4881 / 15121)) (n := 12)
    (lo := (83691331 / 125000000)) (hi := (669530649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001 / 5120) = 1/(5120 / 10001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (83691331 / 125000000) (669530649 / 1000000000) (Real.log (10001 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (10001 / 5120) = -Real.log (5120 / 10001) := by
    rw [show ((10001 / 5120) : ℝ) = ((5120 / 10001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3064446163 / 1000000000) ≤ -Real.log (239 / 5120) ∧
    -Real.log (239 / 5120) ≤ (383055771 / 125000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 239) = 1/(239 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-383055771 / 125000000) (-3064446163 / 1000000000) (Real.log (239 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (669340649 / 1000000000) ≤ -Real.log (51200 / 99991) ∧
    -Real.log (51200 / 99991) ≤ (13386813 / 20000000) := by
  have h := checkLog_sound (w := (48791 / 151191)) (n := 12)
    (lo := (669340649 / 1000000000)) (hi := (13386813 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99991 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99991 / 51200) = 1/(51200 / 99991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (669340649 / 1000000000) (13386813 / 20000000) (Real.log (99991 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99991 / 51200) = -Real.log (51200 / 99991) := by
    rw [show ((99991 / 51200) : ℝ) = ((51200 / 99991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1528263903 / 500000000) ≤ -Real.log (2409 / 51200) ∧
    -Real.log (2409 / 51200) ≤ (3056527811 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 5609)) (n := 12)
    (lo := (141969543 / 500000000)) (hi := (283939087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2409) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2409) = 1/(2409 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3056527811 / 1000000000) (-1528263903 / 500000000) (Real.log (2409 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341578219 / 500000000) ≤ -Real.log (500000 / 990059) ∧
    -Real.log (500000 / 990059) ≤ (683156439 / 1000000000) := by
  have h := checkLog_sound (w := (490059 / 1490059)) (n := 12)
    (lo := (341578219 / 500000000)) (hi := (683156439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990059 / 500000) = 1/(500000 / 990059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341578219 / 500000000) (683156439 / 1000000000) (Real.log (990059 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990059 / 500000) = -Real.log (500000 / 990059) := by
    rw [show ((990059 / 500000) : ℝ) = ((500000 / 990059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (979485119 / 250000000) ≤ -Real.log (9941 / 500000) ∧
    -Real.log (9941 / 500000) ≤ (1958970241 / 500000000) := by
  have h := checkLog_sound (w := (2842 / 12783)) (n := 12)
    (lo := (14131393 / 31250000)) (hi := (452204577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9941) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9941) = 1/(9941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1958970241 / 500000000) (-979485119 / 250000000) (Real.log (9941 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341616347 / 500000000) ≤ -Real.log (1000000 / 1980269) ∧
    -Real.log (1000000 / 1980269) ≤ (136646539 / 200000000) := by
  have h := checkLog_sound (w := (980269 / 2980269)) (n := 12)
    (lo := (341616347 / 500000000)) (hi := (136646539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980269 / 1000000) = 1/(1000000 / 1980269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341616347 / 500000000) (136646539 / 200000000) (Real.log (1980269 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980269 / 1000000) = -Real.log (1000000 / 1980269) := by
    rw [show ((1980269 / 1000000) : ℝ) = ((1000000 / 1980269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3925564273 / 1000000000) ≤ -Real.log (19731 / 1000000) ∧
    -Real.log (19731 / 1000000) ≤ (3925564279 / 1000000000) := by
  have h := checkLog_sound (w := (11519 / 50981)) (n := 12)
    (lo := (459828373 / 1000000000)) (hi := (229914187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19731) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19731) = 1/(19731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3925564279 / 1000000000) (-3925564273 / 1000000000) (Real.log (19731 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170777999 / 250000000) ≤ -Real.log (100000 / 198003) ∧
    -Real.log (100000 / 198003) ≤ (683111997 / 1000000000) := by
  have h := checkLog_sound (w := (98003 / 298003)) (n := 12)
    (lo := (170777999 / 250000000)) (hi := (683111997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198003 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198003 / 100000) = 1/(100000 / 198003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170777999 / 250000000) (683111997 / 1000000000) (Real.log (198003 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (198003 / 100000) = -Real.log (100000 / 198003) := by
    rw [show ((198003 / 100000) : ℝ) = ((100000 / 198003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (122297629 / 31250000) ≤ -Real.log (1997 / 100000) ∧
    -Real.log (1997 / 100000) ≤ (1956762067 / 500000000) := by
  have h := checkLog_sound (w := (564 / 2561)) (n := 12)
    (lo := (111947057 / 250000000)) (hi := (447788229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1997) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1997) = 1/(1997 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1956762067 / 500000000) (-122297629 / 31250000) (Real.log (1997 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683188759 / 1000000000) ≤ -Real.log (500000 / 990091) ∧
    -Real.log (500000 / 990091) ≤ (17079719 / 25000000) := by
  have h := checkLog_sound (w := (490091 / 1490091)) (n := 12)
    (lo := (683188759 / 1000000000)) (hi := (17079719 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990091 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990091 / 500000) = 1/(500000 / 990091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683188759 / 1000000000) (17079719 / 25000000) (Real.log (990091 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990091 / 500000) = -Real.log (500000 / 990091) := by
    rw [show ((990091 / 500000) : ℝ) = ((500000 / 990091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (196058233 / 50000000) ≤ -Real.log (9909 / 500000) ∧
    -Real.log (9909 / 500000) ≤ (1960582333 / 500000000) := by
  have h := checkLog_sound (w := (2858 / 12767)) (n := 12)
    (lo := (11385719 / 25000000)) (hi := (455428761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9909) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9909) = 1/(9909 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1960582333 / 500000000) (-196058233 / 50000000) (Real.log (9909 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2300548457 / 500000000) ≤ -Real.log (62500000000 / 6224593853737) ∧
    -Real.log (62500000000 / 6224593853737) ≤ (4601096921 / 1000000000) := by
  have h := checkLog_sound (w := (2224593853737 / 10224593853737)) (n := 12)
    (lo := (221106917 / 500000000)) (hi := (88442767 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6224593853737 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6224593853737 / 4000000000000) = 1/(62500000000 / 6224593853737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2300548457 / 500000000) (4601096921 / 1000000000) (Real.log (6224593853737 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6224593853737 / 62500000000) = -Real.log (62500000000 / 6224593853737) := by
    rw [show ((6224593853737 / 62500000000) : ℝ) = ((62500000000 / 6224593853737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2304398483 / 500000000) ≤ -Real.log (250000000000 / 25090834220263) ∧
    -Real.log (250000000000 / 25090834220263) ≤ (4608796973 / 1000000000) := by
  have h := checkLog_sound (w := (9090834220263 / 41090834220263)) (n := 12)
    (lo := (224956943 / 500000000)) (hi := (449913887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25090834220263 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25090834220263 / 16000000000000) = 1/(250000000000 / 25090834220263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2304398483 / 500000000) (4608796973 / 1000000000) (Real.log (25090834220263 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25090834220263 / 250000000000) = -Real.log (250000000000 / 25090834220263) := by
    rw [show ((25090834220263 / 250000000000) : ℝ) = ((250000000000 / 25090834220263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1149159031 / 250000000) ≤ -Real.log (500000000000 / 49575112669003) ∧
    -Real.log (500000000000 / 49575112669003) ≤ (4596636131 / 1000000000) := by
  have h := checkLog_sound (w := (17575112669003 / 81575112669003)) (n := 12)
    (lo := (109438261 / 250000000)) (hi := (87550609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49575112669003 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49575112669003 / 32000000000000) = 1/(500000000000 / 49575112669003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1149159031 / 250000000) (4596636131 / 1000000000) (Real.log (49575112669003 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49575112669003 / 500000000000) = -Real.log (500000000000 / 49575112669003) := by
    rw [show ((49575112669003 / 500000000000) : ℝ) = ((500000000000 / 49575112669003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4604353419 / 1000000000) ≤ -Real.log (250000000000 / 24979589262287) ∧
    -Real.log (250000000000 / 24979589262287) ≤ (2302176713 / 500000000) := by
  have h := checkLog_sound (w := (8979589262287 / 40979589262287)) (n := 12)
    (lo := (445470339 / 1000000000)) (hi := (22273517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24979589262287 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24979589262287 / 16000000000000) = 1/(250000000000 / 24979589262287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4604353419 / 1000000000) (2302176713 / 500000000) (Real.log (24979589262287 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24979589262287 / 250000000000) = -Real.log (250000000000 / 24979589262287) := by
    rw [show ((24979589262287 / 250000000000) : ℝ) = ((250000000000 / 24979589262287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0025

end


