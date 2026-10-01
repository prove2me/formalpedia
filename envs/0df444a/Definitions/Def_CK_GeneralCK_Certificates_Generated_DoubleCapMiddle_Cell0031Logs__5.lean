-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0031Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0031Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:37:32.058447+00:00
-- url     : https://prove2.me/theorems/994e22e9-80d4-450c-9abc-8f9572d8de88
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0032Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0032Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0033Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0034Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0035Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0032Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0033Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0034Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0035Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0032Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0033Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0034Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0035Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0031Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0032Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0033Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0034Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0035Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0031Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0031
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

theorem reflection_log_1_neg : (389716751 / 1000000000) ≤ -Real.log (128 / 189) ∧
    -Real.log (128 / 189) ≤ (24357297 / 62500000) := by
  have h := checkLog_sound (w := (61 / 317)) (n := 12)
    (lo := (389716751 / 1000000000)) (hi := (24357297 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 128) = 1/(128 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (389716751 / 1000000000) (24357297 / 62500000) (Real.log (189 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (189 / 128) = -Real.log (128 / 189) := by
    rw [show ((189 / 128) : ℝ) = ((128 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (161834411 / 250000000) ≤ -Real.log (67 / 128) ∧
    -Real.log (67 / 128) ≤ (129467529 / 200000000) := by
  have h := checkLog_sound (w := (61 / 195)) (n := 12)
    (lo := (161834411 / 250000000)) (hi := (129467529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 67) = 1/(67 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-129467529 / 200000000) (-161834411 / 250000000) (Real.log (67 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (77784557 / 200000000) ≤ -Real.log (2560 / 3777) ∧
    -Real.log (2560 / 3777) ≤ (194461393 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 6337)) (n := 12)
    (lo := (77784557 / 200000000)) (hi := (194461393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3777 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3777 / 2560) = 1/(2560 / 3777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (77784557 / 200000000) (194461393 / 500000000) (Real.log (3777 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3777 / 2560) = -Real.log (2560 / 3777) := by
    rw [show ((3777 / 2560) : ℝ) = ((2560 / 3777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32255067 / 50000000) ≤ -Real.log (1343 / 2560) ∧
    -Real.log (1343 / 2560) ≤ (645101341 / 1000000000) := by
  have h := checkLog_sound (w := (1217 / 3903)) (n := 12)
    (lo := (32255067 / 50000000)) (hi := (645101341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1343) = 1/(1343 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-645101341 / 1000000000) (-32255067 / 50000000) (Real.log (1343 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (669430653 / 1000000000) ≤ -Real.log (64 / 125) ∧
    -Real.log (64 / 125) ≤ (334715327 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 64) = 1/(64 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (669430653 / 1000000000) (334715327 / 500000000) (Real.log (125 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (125 / 64) = -Real.log (64 / 125) := by
    rw [show ((125 / 64) : ℝ) = ((64 / 125) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (382533849 / 125000000) ≤ -Real.log (3 / 64) ∧
    -Real.log (3 / 64) ≤ (3060270797 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4 / 3) = 1/(3 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3060270797 / 1000000000) (-382533849 / 125000000) (Real.log (3 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (668229933 / 1000000000) ≤ -Real.log (1280 / 2497) ∧
    -Real.log (1280 / 2497) ≤ (334114967 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 3777)) (n := 12)
    (lo := (668229933 / 1000000000)) (hi := (334114967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 1280) = 1/(1280 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (668229933 / 1000000000) (334114967 / 500000000) (Real.log (2497 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2497 / 1280) = -Real.log (1280 / 2497) := by
    rw [show ((2497 / 1280) : ℝ) = ((1280 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (752870157 / 250000000) ≤ -Real.log (63 / 1280) ∧
    -Real.log (63 / 1280) ≤ (3011480633 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 63) = 1/(63 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3011480633 / 1000000000) (-752870157 / 250000000) (Real.log (63 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (271371113 / 500000000) ≤ -Real.log (1000000 / 1720719) ∧
    -Real.log (1000000 / 1720719) ≤ (542742227 / 1000000000) := by
  have h := checkLog_sound (w := (720719 / 2720719)) (n := 12)
    (lo := (271371113 / 500000000)) (hi := (542742227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1720719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1720719 / 1000000) = 1/(1000000 / 1720719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (271371113 / 500000000) (542742227 / 1000000000) (Real.log (1720719 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1720719 / 1000000) = -Real.log (1000000 / 1720719) := by
    rw [show ((1720719 / 1000000) : ℝ) = ((1000000 / 1720719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (637768417 / 500000000) ≤ -Real.log (279281 / 1000000) ∧
    -Real.log (279281 / 1000000) ≤ (318884209 / 250000000) := by
  have h := checkLog_sound (w := (220719 / 779281)) (n := 12)
    (lo := (291194827 / 500000000)) (hi := (116477931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279281) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 279281) = 1/(279281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-318884209 / 250000000) (-637768417 / 500000000) (Real.log (279281 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (272062787 / 500000000) ≤ -Real.log (1000000 / 1723101) ∧
    -Real.log (1000000 / 1723101) ≤ (21765023 / 40000000) := by
  have h := checkLog_sound (w := (723101 / 2723101)) (n := 12)
    (lo := (272062787 / 500000000)) (hi := (21765023 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1723101 / 1000000) = 1/(1000000 / 1723101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (272062787 / 500000000) (21765023 / 40000000) (Real.log (1723101 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1723101 / 1000000) = -Real.log (1000000 / 1723101) := by
    rw [show ((1723101 / 1000000) : ℝ) = ((1000000 / 1723101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1284102459 / 1000000000) ≤ -Real.log (276899 / 1000000) ∧
    -Real.log (276899 / 1000000) ≤ (1284102461 / 1000000000) := by
  have h := checkLog_sound (w := (223101 / 776899)) (n := 12)
    (lo := (590955279 / 1000000000)) (hi := (7386941 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276899) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 276899) = 1/(276899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1284102461 / 1000000000) (-1284102459 / 1000000000) (Real.log (276899 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (465979919 / 1000000000) ≤ -Real.log (40000 / 63743) ∧
    -Real.log (40000 / 63743) ≤ (5824749 / 12500000) := by
  have h := checkLog_sound (w := (23743 / 103743)) (n := 12)
    (lo := (465979919 / 1000000000)) (hi := (5824749 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63743 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63743 / 40000) = 1/(40000 / 63743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (465979919 / 1000000000) (5824749 / 12500000) (Real.log (63743 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63743 / 40000) = -Real.log (40000 / 63743) := by
    rw [show ((63743 / 40000) : ℝ) = ((40000 / 63743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (225088967 / 250000000) ≤ -Real.log (16257 / 40000) ∧
    -Real.log (16257 / 40000) ≤ (90035587 / 100000000) := by
  have h := checkLog_sound (w := (3743 / 36257)) (n := 12)
    (lo := (12950543 / 62500000)) (hi := (207208689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 16257) = 1/(16257 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-90035587 / 100000000) (-225088967 / 250000000) (Real.log (16257 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (233799119 / 500000000) ≤ -Real.log (250000 / 399039) ∧
    -Real.log (250000 / 399039) ≤ (467598239 / 1000000000) := by
  have h := checkLog_sound (w := (149039 / 649039)) (n := 12)
    (lo := (233799119 / 500000000)) (hi := (467598239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399039 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399039 / 250000) = 1/(250000 / 399039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (233799119 / 500000000) (467598239 / 1000000000) (Real.log (399039 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (399039 / 250000) = -Real.log (250000 / 399039) := by
    rw [show ((399039 / 250000) : ℝ) = ((250000 / 399039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (906726613 / 1000000000) ≤ -Real.log (100961 / 250000) ∧
    -Real.log (100961 / 250000) ≤ (181345323 / 200000000) := by
  have h := checkLog_sound (w := (24039 / 225961)) (n := 12)
    (lo := (213579433 / 1000000000)) (hi := (106789717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100961) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 100961) = 1/(100961 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-181345323 / 200000000) (-906726613 / 1000000000) (Real.log (100961 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1818279061 / 1000000000) ≤ -Real.log (500000000000 / 3080623100031) ∧
    -Real.log (500000000000 / 3080623100031) ≤ (227284883 / 125000000) := by
  have h := checkLog_sound (w := (1080623100031 / 5080623100031)) (n := 12)
    (lo := (431984701 / 1000000000)) (hi := (215992351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3080623100031 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3080623100031 / 2000000000000) = 1/(500000000000 / 3080623100031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1818279061 / 1000000000) (227284883 / 125000000) (Real.log (3080623100031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3080623100031 / 500000000000) = -Real.log (500000000000 / 3080623100031) := by
    rw [show ((3080623100031 / 500000000000) : ℝ) = ((500000000000 / 3080623100031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1828228033 / 1000000000) ≤ -Real.log (500000000000 / 3111425104461) ∧
    -Real.log (500000000000 / 3111425104461) ≤ (457057009 / 250000000) := by
  have h := checkLog_sound (w := (1111425104461 / 5111425104461)) (n := 12)
    (lo := (441933673 / 1000000000)) (hi := (220966837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111425104461 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3111425104461 / 2000000000000) = 1/(500000000000 / 3111425104461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1828228033 / 1000000000) (457057009 / 250000000) (Real.log (3111425104461 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3111425104461 / 500000000000) = -Real.log (500000000000 / 3111425104461) := by
    rw [show ((3111425104461 / 500000000000) : ℝ) = ((500000000000 / 3111425104461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (341583947 / 250000000) ≤ -Real.log (12500000000 / 49011964077) ∧
    -Real.log (12500000000 / 49011964077) ≤ (136633579 / 100000000) := by
  have h := checkLog_sound (w := (24011964077 / 74011964077)) (n := 12)
    (lo := (2629643 / 3906250)) (hi := (673188609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49011964077 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(49011964077 / 25000000000) = 1/(12500000000 / 49011964077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (341583947 / 250000000) (136633579 / 100000000) (Real.log (49011964077 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49011964077 / 12500000000) = -Real.log (12500000000 / 49011964077) := by
    rw [show ((49011964077 / 12500000000) : ℝ) = ((12500000000 / 49011964077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (343581213 / 250000000) ≤ -Real.log (500000000000 / 1976203682611) ∧
    -Real.log (500000000000 / 1976203682611) ≤ (687162427 / 500000000) := by
  have h := checkLog_sound (w := (976203682611 / 2976203682611)) (n := 12)
    (lo := (85147209 / 125000000)) (hi := (681177673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976203682611 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1976203682611 / 1000000000000) = 1/(500000000000 / 1976203682611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (343581213 / 250000000) (687162427 / 500000000) (Real.log (1976203682611 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1976203682611 / 500000000000) = -Real.log (500000000000 / 1976203682611) := by
    rw [show ((1976203682611 / 500000000000) : ℝ) = ((500000000000 / 1976203682611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0031

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0032Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0032
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

theorem reflection_log_1_neg : (77784557 / 200000000) ≤ -Real.log (2560 / 3777) ∧
    -Real.log (2560 / 3777) ≤ (194461393 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 6337)) (n := 12)
    (lo := (77784557 / 200000000)) (hi := (194461393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3777 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3777 / 2560) = 1/(2560 / 3777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (77784557 / 200000000) (194461393 / 500000000) (Real.log (3777 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3777 / 2560) = -Real.log (2560 / 3777) := by
    rw [show ((3777 / 2560) : ℝ) = ((2560 / 3777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32255067 / 50000000) ≤ -Real.log (1343 / 2560) ∧
    -Real.log (1343 / 2560) ≤ (645101341 / 1000000000) := by
  have h := checkLog_sound (w := (1217 / 3903)) (n := 12)
    (lo := (32255067 / 50000000)) (hi := (645101341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1343) = 1/(1343 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-645101341 / 1000000000) (-32255067 / 50000000) (Real.log (1343 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (97032047 / 250000000) ≤ -Real.log (1280 / 1887) ∧
    -Real.log (1280 / 1887) ≤ (388128189 / 1000000000) := by
  have h := checkLog_sound (w := (607 / 3167)) (n := 12)
    (lo := (97032047 / 250000000)) (hi := (388128189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887 / 1280) = 1/(1280 / 1887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (97032047 / 250000000) (388128189 / 1000000000) (Real.log (1887 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1887 / 1280) = -Real.log (1280 / 1887) := by
    rw [show ((1887 / 1280) : ℝ) = ((1280 / 1887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (642870027 / 1000000000) ≤ -Real.log (673 / 1280) ∧
    -Real.log (673 / 1280) ≤ (160717507 / 250000000) := by
  have h := checkLog_sound (w := (607 / 1953)) (n := 12)
    (lo := (642870027 / 1000000000)) (hi := (160717507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 673) = 1/(673 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-160717507 / 250000000) (-642870027 / 1000000000) (Real.log (673 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (668229933 / 1000000000) ≤ -Real.log (1280 / 2497) ∧
    -Real.log (1280 / 2497) ≤ (334114967 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 3777)) (n := 12)
    (lo := (668229933 / 1000000000)) (hi := (334114967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 1280) = 1/(1280 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (668229933 / 1000000000) (334114967 / 500000000) (Real.log (2497 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2497 / 1280) = -Real.log (1280 / 2497) := by
    rw [show ((2497 / 1280) : ℝ) = ((1280 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (752870157 / 250000000) ≤ -Real.log (63 / 1280) ∧
    -Real.log (63 / 1280) ≤ (3011480633 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 63) = 1/(63 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3011480633 / 1000000000) (-752870157 / 250000000) (Real.log (63 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667027769 / 1000000000) ≤ -Real.log (640 / 1247) ∧
    -Real.log (640 / 1247) ≤ (66702777 / 100000000) := by
  have h := checkLog_sound (w := (607 / 1887)) (n := 12)
    (lo := (667027769 / 1000000000)) (hi := (66702777 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 640) = 1/(640 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667027769 / 1000000000) (66702777 / 100000000) (Real.log (1247 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1247 / 640) = -Real.log (640 / 1247) := by
    rw [show ((1247 / 640) : ℝ) = ((640 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (741240153 / 250000000) ≤ -Real.log (33 / 640) ∧
    -Real.log (33 / 640) ≤ (2964960617 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 33) = 1/(33 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2964960617 / 1000000000) (-741240153 / 250000000) (Real.log (33 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (541368601 / 1000000000) ≤ -Real.log (1000000 / 1718357) ∧
    -Real.log (1000000 / 1718357) ≤ (270684301 / 500000000) := by
  have h := checkLog_sound (w := (718357 / 2718357)) (n := 12)
    (lo := (541368601 / 1000000000)) (hi := (270684301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1718357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1718357 / 1000000) = 1/(1000000 / 1718357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (541368601 / 1000000000) (270684301 / 500000000) (Real.log (1718357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1718357 / 1000000) = -Real.log (1000000 / 1718357) := by
    rw [show ((1718357 / 1000000) : ℝ) = ((1000000 / 1718357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (633557483 / 500000000) ≤ -Real.log (281643 / 1000000) ∧
    -Real.log (281643 / 1000000) ≤ (158389371 / 125000000) := by
  have h := checkLog_sound (w := (218357 / 781643)) (n := 12)
    (lo := (286983893 / 500000000)) (hi := (573967787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 281643) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 281643) = 1/(281643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158389371 / 125000000) (-633557483 / 500000000) (Real.log (281643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (542742807 / 1000000000) ≤ -Real.log (12500 / 21509) ∧
    -Real.log (12500 / 21509) ≤ (67842851 / 125000000) := by
  have h := checkLog_sound (w := (9009 / 34009)) (n := 12)
    (lo := (542742807 / 1000000000)) (hi := (67842851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21509 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21509 / 12500) = 1/(12500 / 21509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (542742807 / 1000000000) (67842851 / 125000000) (Real.log (21509 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (21509 / 12500) = -Real.log (12500 / 21509) := by
    rw [show ((21509 / 12500) : ℝ) = ((12500 / 21509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (255108083 / 200000000) ≤ -Real.log (3491 / 12500) ∧
    -Real.log (3491 / 12500) ≤ (1275540417 / 1000000000) := by
  have h := checkLog_sound (w := (2759 / 9741)) (n := 12)
    (lo := (116478647 / 200000000)) (hi := (145598309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3491) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 3491) = 1/(3491 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1275540417 / 1000000000) (-255108083 / 200000000) (Real.log (3491 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (116093987 / 250000000) ≤ -Real.log (1000000 / 1591021) ∧
    -Real.log (1000000 / 1591021) ≤ (464375949 / 1000000000) := by
  have h := checkLog_sound (w := (591021 / 2591021)) (n := 12)
    (lo := (116093987 / 250000000)) (hi := (464375949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1591021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1591021 / 1000000) = 1/(1000000 / 1591021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (116093987 / 250000000) (464375949 / 1000000000) (Real.log (1591021 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1591021 / 1000000) = -Real.log (1000000 / 1591021) := by
    rw [show ((1591021 / 1000000) : ℝ) = ((1000000 / 1591021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (223522867 / 250000000) ≤ -Real.log (408979 / 1000000) ∧
    -Real.log (408979 / 1000000) ≤ (89409147 / 100000000) := by
  have h := checkLog_sound (w := (91021 / 908979)) (n := 12)
    (lo := (6279509 / 31250000)) (hi := (200944289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408979) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 408979) = 1/(408979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-89409147 / 100000000) (-223522867 / 250000000) (Real.log (408979 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (465980547 / 1000000000) ≤ -Real.log (125000 / 199197) ∧
    -Real.log (125000 / 199197) ≤ (116495137 / 250000000) := by
  have h := checkLog_sound (w := (74197 / 324197)) (n := 12)
    (lo := (465980547 / 1000000000)) (hi := (116495137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199197 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199197 / 125000) = 1/(125000 / 199197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (465980547 / 1000000000) (116495137 / 250000000) (Real.log (199197 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (199197 / 125000) = -Real.log (125000 / 199197) := by
    rw [show ((199197 / 125000) : ℝ) = ((125000 / 199197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (112544791 / 125000000) ≤ -Real.log (50803 / 125000) ∧
    -Real.log (50803 / 125000) ≤ (90035833 / 100000000) := by
  have h := checkLog_sound (w := (11697 / 113303)) (n := 12)
    (lo := (51802787 / 250000000)) (hi := (207211149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50803) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50803) = 1/(50803 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90035833 / 100000000) (-112544791 / 125000000) (Real.log (50803 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (113030223 / 62500000) ≤ -Real.log (250000000000 / 1525297095969) ∧
    -Real.log (250000000000 / 1525297095969) ≤ (1808483571 / 1000000000) := by
  have h := checkLog_sound (w := (525297095969 / 2525297095969)) (n := 12)
    (lo := (52773651 / 125000000)) (hi := (422189209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1525297095969 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1525297095969 / 1000000000000) = 1/(250000000000 / 1525297095969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (113030223 / 62500000) (1808483571 / 1000000000) (Real.log (1525297095969 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1525297095969 / 250000000000) = -Real.log (250000000000 / 1525297095969) := by
    rw [show ((1525297095969 / 250000000000) : ℝ) = ((250000000000 / 1525297095969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (909141611 / 500000000) ≤ -Real.log (25000000000 / 154031796047) ∧
    -Real.log (25000000000 / 154031796047) ≤ (72731329 / 40000000) := by
  have h := checkLog_sound (w := (54031796047 / 254031796047)) (n := 12)
    (lo := (215994431 / 500000000)) (hi := (431988863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154031796047 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(154031796047 / 100000000000) = 1/(25000000000 / 154031796047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (909141611 / 500000000) (72731329 / 40000000) (Real.log (154031796047 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154031796047 / 25000000000) = -Real.log (25000000000 / 154031796047) := by
    rw [show ((154031796047 / 25000000000) : ℝ) = ((25000000000 / 154031796047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (169808427 / 125000000) ≤ -Real.log (62500000000 / 243139164847) ∧
    -Real.log (62500000000 / 243139164847) ≤ (679233709 / 500000000) := by
  have h := checkLog_sound (w := (118139164847 / 368139164847)) (n := 12)
    (lo := (166330059 / 250000000)) (hi := (665320237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243139164847 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(243139164847 / 125000000000) = 1/(62500000000 / 243139164847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (169808427 / 125000000) (679233709 / 500000000) (Real.log (243139164847 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (243139164847 / 62500000000) = -Real.log (62500000000 / 243139164847) := by
    rw [show ((243139164847 / 62500000000) : ℝ) = ((62500000000 / 243139164847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (341584719 / 250000000) ≤ -Real.log (500000000000 / 1960484617051) ∧
    -Real.log (500000000000 / 1960484617051) ≤ (683169439 / 500000000) := by
  have h := checkLog_sound (w := (960484617051 / 2960484617051)) (n := 12)
    (lo := (42074481 / 62500000)) (hi := (673191697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960484617051 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1960484617051 / 1000000000000) = 1/(500000000000 / 1960484617051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (341584719 / 250000000) (683169439 / 500000000) (Real.log (1960484617051 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1960484617051 / 500000000000) = -Real.log (500000000000 / 1960484617051) := by
    rw [show ((1960484617051 / 500000000000) : ℝ) = ((500000000000 / 1960484617051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0032

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0033Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0033
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

theorem reflection_log_1_neg : (97032047 / 250000000) ≤ -Real.log (1280 / 1887) ∧
    -Real.log (1280 / 1887) ≤ (388128189 / 1000000000) := by
  have h := checkLog_sound (w := (607 / 3167)) (n := 12)
    (lo := (97032047 / 250000000)) (hi := (388128189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887 / 1280) = 1/(1280 / 1887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (97032047 / 250000000) (388128189 / 1000000000) (Real.log (1887 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1887 / 1280) = -Real.log (1280 / 1887) := by
    rw [show ((1887 / 1280) : ℝ) = ((1280 / 1887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (642870027 / 1000000000) ≤ -Real.log (673 / 1280) ∧
    -Real.log (673 / 1280) ≤ (160717507 / 250000000) := by
  have h := checkLog_sound (w := (607 / 1953)) (n := 12)
    (lo := (642870027 / 1000000000)) (hi := (160717507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 673) = 1/(673 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-160717507 / 250000000) (-642870027 / 1000000000) (Real.log (673 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (387332959 / 1000000000) ≤ -Real.log (2560 / 3771) ∧
    -Real.log (2560 / 3771) ≤ (2420831 / 6250000) := by
  have h := checkLog_sound (w := (1211 / 6331)) (n := 12)
    (lo := (387332959 / 1000000000)) (hi := (2420831 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3771 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3771 / 2560) = 1/(2560 / 3771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (387332959 / 1000000000) (2420831 / 6250000) (Real.log (3771 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3771 / 2560) = -Real.log (2560 / 3771) := by
    rw [show ((3771 / 2560) : ℝ) = ((2560 / 3771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (640643681 / 1000000000) ≤ -Real.log (1349 / 2560) ∧
    -Real.log (1349 / 2560) ≤ (320321841 / 500000000) := by
  have h := checkLog_sound (w := (1211 / 3909)) (n := 12)
    (lo := (640643681 / 1000000000)) (hi := (320321841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1349) = 1/(1349 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-320321841 / 500000000) (-640643681 / 1000000000) (Real.log (1349 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667027769 / 1000000000) ≤ -Real.log (640 / 1247) ∧
    -Real.log (640 / 1247) ≤ (66702777 / 100000000) := by
  have h := checkLog_sound (w := (607 / 1887)) (n := 12)
    (lo := (667027769 / 1000000000)) (hi := (66702777 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 640) = 1/(640 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (667027769 / 1000000000) (66702777 / 100000000) (Real.log (1247 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1247 / 640) = -Real.log (640 / 1247) := by
    rw [show ((1247 / 640) : ℝ) = ((640 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (741240153 / 250000000) ≤ -Real.log (33 / 640) ∧
    -Real.log (33 / 640) ≤ (2964960617 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 33) = 1/(33 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2964960617 / 1000000000) (-741240153 / 250000000) (Real.log (33 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332912079 / 500000000) ≤ -Real.log (1280 / 2491) ∧
    -Real.log (1280 / 2491) ≤ (665824159 / 1000000000) := by
  have h := checkLog_sound (w := (1211 / 3771)) (n := 12)
    (lo := (332912079 / 500000000)) (hi := (665824159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 1280) = 1/(1280 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (332912079 / 500000000) (665824159 / 1000000000) (Real.log (2491 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2491 / 1280) = -Real.log (1280 / 2491) := by
    rw [show ((2491 / 1280) : ℝ) = ((1280 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58410177 / 20000000) ≤ -Real.log (69 / 1280) ∧
    -Real.log (69 / 1280) ≤ (584101771 / 200000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 69) = 1/(69 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-584101771 / 200000000) (-58410177 / 20000000) (Real.log (69 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (270001497 / 500000000) ≤ -Real.log (250000 / 429003) ∧
    -Real.log (250000 / 429003) ≤ (108000599 / 200000000) := by
  have h := checkLog_sound (w := (179003 / 679003)) (n := 12)
    (lo := (270001497 / 500000000)) (hi := (108000599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429003 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429003 / 250000) = 1/(250000 / 429003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (270001497 / 500000000) (108000599 / 200000000) (Real.log (429003 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (429003 / 250000) = -Real.log (250000 / 429003) := by
    rw [show ((429003 / 250000) : ℝ) = ((250000 / 429003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (629411647 / 500000000) ≤ -Real.log (70997 / 250000) ∧
    -Real.log (70997 / 250000) ≤ (9834557 / 7812500) := by
  have h := checkLog_sound (w := (54003 / 195997)) (n := 12)
    (lo := (282838057 / 500000000)) (hi := (113135223 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70997) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 70997) = 1/(70997 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9834557 / 7812500) (-629411647 / 500000000) (Real.log (70997 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (541369183 / 1000000000) ≤ -Real.log (500000 / 859179) ∧
    -Real.log (500000 / 859179) ≤ (16917787 / 31250000) := by
  have h := checkLog_sound (w := (359179 / 1359179)) (n := 12)
    (lo := (541369183 / 1000000000)) (hi := (16917787 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859179 / 500000) = 1/(500000 / 859179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (541369183 / 1000000000) (16917787 / 31250000) (Real.log (859179 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (859179 / 500000) = -Real.log (500000 / 859179) := by
    rw [show ((859179 / 500000) : ℝ) = ((500000 / 859179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1267118517 / 1000000000) ≤ -Real.log (140821 / 500000) ∧
    -Real.log (140821 / 500000) ≤ (1267118519 / 1000000000) := by
  have h := checkLog_sound (w := (109179 / 390821)) (n := 12)
    (lo := (573971337 / 1000000000)) (hi := (286985669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 140821) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 140821) = 1/(140821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1267118519 / 1000000000) (-1267118517 / 1000000000) (Real.log (140821 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (231392569 / 500000000) ≤ -Real.log (250000 / 397123) ∧
    -Real.log (250000 / 397123) ≤ (462785139 / 1000000000) := by
  have h := checkLog_sound (w := (147123 / 647123)) (n := 12)
    (lo := (231392569 / 500000000)) (hi := (462785139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397123 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397123 / 250000) = 1/(250000 / 397123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (231392569 / 500000000) (462785139 / 1000000000) (Real.log (397123 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (397123 / 250000) = -Real.log (250000 / 397123) := by
    rw [show ((397123 / 250000) : ℝ) = ((250000 / 397123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (887926817 / 1000000000) ≤ -Real.log (102877 / 250000) ∧
    -Real.log (102877 / 250000) ≤ (887926819 / 1000000000) := by
  have h := checkLog_sound (w := (22123 / 227877)) (n := 12)
    (lo := (194779637 / 1000000000)) (hi := (97389819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102877) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 102877) = 1/(102877 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-887926819 / 1000000000) (-887926817 / 1000000000) (Real.log (102877 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (464376577 / 1000000000) ≤ -Real.log (500000 / 795511) ∧
    -Real.log (500000 / 795511) ≤ (232188289 / 500000000) := by
  have h := checkLog_sound (w := (295511 / 1295511)) (n := 12)
    (lo := (464376577 / 1000000000)) (hi := (232188289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795511 / 500000) = 1/(500000 / 795511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (464376577 / 1000000000) (232188289 / 500000000) (Real.log (795511 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (795511 / 500000) = -Real.log (500000 / 795511) := by
    rw [show ((795511 / 500000) : ℝ) = ((500000 / 795511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (894093913 / 1000000000) ≤ -Real.log (204489 / 500000) ∧
    -Real.log (204489 / 500000) ≤ (178818783 / 200000000) := by
  have h := checkLog_sound (w := (45511 / 454489)) (n := 12)
    (lo := (200946733 / 1000000000)) (hi := (100473367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204489) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 204489) = 1/(204489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-178818783 / 200000000) (-894093913 / 1000000000) (Real.log (204489 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (112426643 / 62500000) ≤ -Real.log (250000000000 / 1510637773427) ∧
    -Real.log (250000000000 / 1510637773427) ≤ (1798826291 / 1000000000) := by
  have h := checkLog_sound (w := (510637773427 / 2510637773427)) (n := 12)
    (lo := (51566491 / 125000000)) (hi := (412531929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510637773427 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1510637773427 / 1000000000000) = 1/(250000000000 / 1510637773427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (112426643 / 62500000) (1798826291 / 1000000000) (Real.log (1510637773427 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1510637773427 / 250000000000) = -Real.log (250000000000 / 1510637773427) := by
    rw [show ((1510637773427 / 250000000000) : ℝ) = ((250000000000 / 1510637773427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18084877 / 10000000) ≤ -Real.log (250000000000 / 1525303399351) ∧
    -Real.log (250000000000 / 1525303399351) ≤ (1808487703 / 1000000000) := by
  have h := checkLog_sound (w := (525303399351 / 2525303399351)) (n := 12)
    (lo := (21109667 / 50000000)) (hi := (422193341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1525303399351 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1525303399351 / 1000000000000) = 1/(250000000000 / 1525303399351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18084877 / 10000000) (1808487703 / 1000000000) (Real.log (1525303399351 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1525303399351 / 250000000000) = -Real.log (250000000000 / 1525303399351) := by
    rw [show ((1525303399351 / 250000000000) : ℝ) = ((250000000000 / 1525303399351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (270142391 / 200000000) ≤ -Real.log (31250000000 / 120630400867) ∧
    -Real.log (31250000000 / 120630400867) ≤ (1350711957 / 1000000000) := by
  have h := checkLog_sound (w := (58130400867 / 183130400867)) (n := 12)
    (lo := (26302591 / 40000000)) (hi := (82195597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120630400867 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(120630400867 / 62500000000) = 1/(31250000000 / 120630400867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (270142391 / 200000000) (1350711957 / 1000000000) (Real.log (120630400867 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (120630400867 / 31250000000) = -Real.log (31250000000 / 120630400867) := by
    rw [show ((120630400867 / 31250000000) : ℝ) = ((31250000000 / 120630400867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (135847049 / 100000000) ≤ -Real.log (500000000000 / 1945119297371) ∧
    -Real.log (500000000000 / 1945119297371) ≤ (339617623 / 250000000) := by
  have h := checkLog_sound (w := (945119297371 / 2945119297371)) (n := 12)
    (lo := (66532331 / 100000000)) (hi := (665323311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945119297371 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1945119297371 / 1000000000000) = 1/(500000000000 / 1945119297371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (135847049 / 100000000) (339617623 / 250000000) (Real.log (1945119297371 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1945119297371 / 500000000000) = -Real.log (500000000000 / 1945119297371) := by
    rw [show ((1945119297371 / 500000000000) : ℝ) = ((500000000000 / 1945119297371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0033

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0034Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0034
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

theorem reflection_log_1_neg : (387332959 / 1000000000) ≤ -Real.log (2560 / 3771) ∧
    -Real.log (2560 / 3771) ≤ (2420831 / 6250000) := by
  have h := checkLog_sound (w := (1211 / 6331)) (n := 12)
    (lo := (387332959 / 1000000000)) (hi := (2420831 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3771 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3771 / 2560) = 1/(2560 / 3771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (387332959 / 1000000000) (2420831 / 6250000) (Real.log (3771 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3771 / 2560) = -Real.log (2560 / 3771) := by
    rw [show ((3771 / 2560) : ℝ) = ((2560 / 3771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (640643681 / 1000000000) ≤ -Real.log (1349 / 2560) ∧
    -Real.log (1349 / 2560) ≤ (320321841 / 500000000) := by
  have h := checkLog_sound (w := (1211 / 3909)) (n := 12)
    (lo := (640643681 / 1000000000)) (hi := (320321841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1349) = 1/(1349 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-320321841 / 500000000) (-640643681 / 1000000000) (Real.log (1349 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (193268549 / 500000000) ≤ -Real.log (320 / 471) ∧
    -Real.log (320 / 471) ≤ (386537099 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 791)) (n := 12)
    (lo := (193268549 / 500000000)) (hi := (386537099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 320) = 1/(320 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (193268549 / 500000000) (386537099 / 1000000000) (Real.log (471 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (471 / 320) = -Real.log (320 / 471) := by
    rw [show ((471 / 320) : ℝ) = ((320 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15960557 / 25000000) ≤ -Real.log (169 / 320) ∧
    -Real.log (169 / 320) ≤ (638422281 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 169) = 1/(169 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-638422281 / 1000000000) (-15960557 / 25000000) (Real.log (169 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332912079 / 500000000) ≤ -Real.log (1280 / 2491) ∧
    -Real.log (1280 / 2491) ≤ (665824159 / 1000000000) := by
  have h := checkLog_sound (w := (1211 / 3771)) (n := 12)
    (lo := (332912079 / 500000000)) (hi := (665824159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 1280) = 1/(1280 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (332912079 / 500000000) (665824159 / 1000000000) (Real.log (2491 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2491 / 1280) = -Real.log (1280 / 2491) := by
    rw [show ((2491 / 1280) : ℝ) = ((1280 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58410177 / 20000000) ≤ -Real.log (69 / 1280) ∧
    -Real.log (69 / 1280) ≤ (584101771 / 200000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 69) = 1/(69 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-584101771 / 200000000) (-58410177 / 20000000) (Real.log (69 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83077387 / 125000000) ≤ -Real.log (160 / 311) ∧
    -Real.log (160 / 311) ≤ (664619097 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 471)) (n := 12)
    (lo := (83077387 / 125000000)) (hi := (664619097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311 / 160) = 1/(160 / 311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83077387 / 125000000) (664619097 / 1000000000) (Real.log (311 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (311 / 160) = -Real.log (160 / 311) := by
    rw [show ((311 / 160) : ℝ) = ((160 / 311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (575589847 / 200000000) ≤ -Real.log (9 / 160) ∧
    -Real.log (9 / 160) ≤ (71948731 / 25000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 9) = 1/(9 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71948731 / 25000000) (-575589847 / 200000000) (Real.log (9 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (538645439 / 1000000000) ≤ -Real.log (250000 / 428421) ∧
    -Real.log (250000 / 428421) ≤ (1683267 / 3125000) := by
  have h := checkLog_sound (w := (178421 / 678421)) (n := 12)
    (lo := (538645439 / 1000000000)) (hi := (1683267 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((428421 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(428421 / 250000) = 1/(250000 / 428421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (538645439 / 1000000000) (1683267 / 3125000) (Real.log (428421 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (428421 / 250000) = -Real.log (250000 / 428421) := by
    rw [show ((428421 / 250000) : ℝ) = ((250000 / 428421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (625329591 / 500000000) ≤ -Real.log (71579 / 250000) ∧
    -Real.log (71579 / 250000) ≤ (78166199 / 62500000) := by
  have h := checkLog_sound (w := (53421 / 196579)) (n := 12)
    (lo := (278756001 / 500000000)) (hi := (557512003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 71579) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 71579) = 1/(71579 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-78166199 / 62500000) (-625329591 / 500000000) (Real.log (71579 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67500447 / 125000000) ≤ -Real.log (1000000 / 1716013) ∧
    -Real.log (1000000 / 1716013) ≤ (540003577 / 1000000000) := by
  have h := checkLog_sound (w := (716013 / 2716013)) (n := 12)
    (lo := (67500447 / 125000000)) (hi := (540003577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1716013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1716013 / 1000000) = 1/(1000000 / 1716013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67500447 / 125000000) (540003577 / 1000000000) (Real.log (1716013 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1716013 / 1000000) = -Real.log (1000000 / 1716013) := by
    rw [show ((1716013 / 1000000) : ℝ) = ((1000000 / 1716013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (251765363 / 200000000) ≤ -Real.log (283987 / 1000000) ∧
    -Real.log (283987 / 1000000) ≤ (1258826817 / 1000000000) := by
  have h := checkLog_sound (w := (216013 / 783987)) (n := 12)
    (lo := (113135927 / 200000000)) (hi := (141419909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 283987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 283987) = 1/(283987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1258826817 / 1000000000) (-251765363 / 200000000) (Real.log (283987 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (230603463 / 500000000) ≤ -Real.log (1000000 / 1585987) ∧
    -Real.log (1000000 / 1585987) ≤ (461206927 / 1000000000) := by
  have h := checkLog_sound (w := (585987 / 2585987)) (n := 12)
    (lo := (230603463 / 500000000)) (hi := (461206927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1585987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1585987 / 1000000) = 1/(1000000 / 1585987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (230603463 / 500000000) (461206927 / 1000000000) (Real.log (1585987 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1585987 / 1000000) = -Real.log (1000000 / 1585987) := by
    rw [show ((1585987 / 1000000) : ℝ) = ((1000000 / 1585987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (55116119 / 62500000) ≤ -Real.log (414013 / 1000000) ∧
    -Real.log (414013 / 1000000) ≤ (440928953 / 500000000) := by
  have h := checkLog_sound (w := (85987 / 914013)) (n := 12)
    (lo := (47177681 / 250000000)) (hi := (7548429 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 414013) = 1/(414013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-440928953 / 500000000) (-55116119 / 62500000) (Real.log (414013 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (57848221 / 125000000) ≤ -Real.log (1000000 / 1588493) ∧
    -Real.log (1000000 / 1588493) ≤ (462785769 / 1000000000) := by
  have h := checkLog_sound (w := (588493 / 2588493)) (n := 12)
    (lo := (57848221 / 125000000)) (hi := (462785769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1588493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1588493 / 1000000) = 1/(1000000 / 1588493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (57848221 / 125000000) (462785769 / 1000000000) (Real.log (1588493 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1588493 / 1000000) = -Real.log (1000000 / 1588493) := by
    rw [show ((1588493 / 1000000) : ℝ) = ((1000000 / 1588493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (887929247 / 1000000000) ≤ -Real.log (411507 / 1000000) ∧
    -Real.log (411507 / 1000000) ≤ (887929249 / 1000000000) := by
  have h := checkLog_sound (w := (88493 / 911507)) (n := 12)
    (lo := (194782067 / 1000000000)) (hi := (48695517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 411507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 411507) = 1/(411507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-887929249 / 1000000000) (-887929247 / 1000000000) (Real.log (411507 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1789304621 / 1000000000) ≤ -Real.log (250000000000 / 1496322245351) ∧
    -Real.log (250000000000 / 1496322245351) ≤ (111831539 / 62500000) := by
  have h := checkLog_sound (w := (496322245351 / 2496322245351)) (n := 12)
    (lo := (403010261 / 1000000000)) (hi := (201505131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1496322245351 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1496322245351 / 1000000000000) = 1/(250000000000 / 1496322245351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1789304621 / 1000000000) (111831539 / 62500000) (Real.log (1496322245351 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1496322245351 / 250000000000) = -Real.log (250000000000 / 1496322245351) := by
    rw [show ((1496322245351 / 250000000000) : ℝ) = ((250000000000 / 1496322245351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (224853799 / 125000000) ≤ -Real.log (12500000000 / 75532198657) ∧
    -Real.log (12500000000 / 75532198657) ≤ (359766079 / 200000000) := by
  have h := checkLog_sound (w := (25532198657 / 125532198657)) (n := 12)
    (lo := (12891751 / 31250000)) (hi := (412536033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75532198657 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(75532198657 / 50000000000) = 1/(12500000000 / 75532198657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (224853799 / 125000000) (359766079 / 200000000) (Real.log (75532198657 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (75532198657 / 12500000000) = -Real.log (12500000000 / 75532198657) := by
    rw [show ((75532198657 / 12500000000) : ℝ) = ((12500000000 / 75532198657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (134306483 / 100000000) ≤ -Real.log (100000000000 / 383076618367) ∧
    -Real.log (100000000000 / 383076618367) ≤ (5246347 / 3906250) := by
  have h := checkLog_sound (w := (183076618367 / 583076618367)) (n := 12)
    (lo := (12998353 / 20000000)) (hi := (649917651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383076618367 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(383076618367 / 200000000000) = 1/(100000000000 / 383076618367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (134306483 / 100000000) (5246347 / 3906250) (Real.log (383076618367 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (383076618367 / 100000000000) = -Real.log (100000000000 / 383076618367) := by
    rw [show ((383076618367 / 100000000000) : ℝ) = ((100000000000 / 383076618367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (270143003 / 200000000) ≤ -Real.log (62500000000 / 241261539901) ∧
    -Real.log (62500000000 / 241261539901) ≤ (1350715017 / 1000000000) := by
  have h := checkLog_sound (w := (116261539901 / 366261539901)) (n := 12)
    (lo := (131513567 / 200000000)) (hi := (164391959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241261539901 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(241261539901 / 125000000000) = 1/(62500000000 / 241261539901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (270143003 / 200000000) (1350715017 / 1000000000) (Real.log (241261539901 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (241261539901 / 62500000000) = -Real.log (62500000000 / 241261539901) := by
    rw [show ((241261539901 / 62500000000) : ℝ) = ((62500000000 / 241261539901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0034

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0035Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0035
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

theorem reflection_log_1_neg : (193268549 / 500000000) ≤ -Real.log (320 / 471) ∧
    -Real.log (320 / 471) ≤ (386537099 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 791)) (n := 12)
    (lo := (193268549 / 500000000)) (hi := (386537099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 320) = 1/(320 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (193268549 / 500000000) (386537099 / 1000000000) (Real.log (471 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (471 / 320) = -Real.log (320 / 471) := by
    rw [show ((471 / 320) : ℝ) = ((320 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15960557 / 25000000) ≤ -Real.log (169 / 320) ∧
    -Real.log (169 / 320) ≤ (638422281 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 169) = 1/(169 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-638422281 / 1000000000) (-15960557 / 25000000) (Real.log (169 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (192870301 / 500000000) ≤ -Real.log (512 / 753) ∧
    -Real.log (512 / 753) ≤ (385740603 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1265)) (n := 12)
    (lo := (192870301 / 500000000)) (hi := (385740603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753 / 512) = 1/(512 / 753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (192870301 / 500000000) (385740603 / 1000000000) (Real.log (753 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (753 / 512) = -Real.log (512 / 753) := by
    rw [show ((753 / 512) : ℝ) = ((512 / 753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (159051451 / 250000000) ≤ -Real.log (271 / 512) ∧
    -Real.log (271 / 512) ≤ (127241161 / 200000000) := by
  have h := checkLog_sound (w := (241 / 783)) (n := 12)
    (lo := (159051451 / 250000000)) (hi := (127241161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 271) = 1/(271 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127241161 / 200000000) (-159051451 / 250000000) (Real.log (271 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (83077387 / 125000000) ≤ -Real.log (160 / 311) ∧
    -Real.log (160 / 311) ≤ (664619097 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 471)) (n := 12)
    (lo := (83077387 / 125000000)) (hi := (664619097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311 / 160) = 1/(160 / 311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (83077387 / 125000000) (664619097 / 1000000000) (Real.log (311 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (311 / 160) = -Real.log (160 / 311) := by
    rw [show ((311 / 160) : ℝ) = ((160 / 311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (575589847 / 200000000) ≤ -Real.log (9 / 160) ∧
    -Real.log (9 / 160) ≤ (71948731 / 25000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 9) = 1/(9 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71948731 / 25000000) (-575589847 / 200000000) (Real.log (9 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
    -Real.log (256 / 497) ≤ (331706291 / 500000000) := by
  have h := checkLog_sound (w := (241 / 753)) (n := 12)
    (lo := (663412581 / 1000000000)) (hi := (331706291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 256) = 1/(256 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
    -Real.log (15 / 256) ≤ (1418563623 / 500000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 15) = 1/(15 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (537294803 / 1000000000) ≤ -Real.log (1000000 / 1711371) ∧
    -Real.log (1000000 / 1711371) ≤ (134323701 / 250000000) := by
  have h := checkLog_sound (w := (711371 / 2711371)) (n := 12)
    (lo := (537294803 / 1000000000)) (hi := (134323701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1711371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1711371 / 1000000) = 1/(1000000 / 1711371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (537294803 / 1000000000) (134323701 / 250000000) (Real.log (1711371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1711371 / 1000000) = -Real.log (1000000 / 1711371) := by
    rw [show ((1711371 / 1000000) : ℝ) = ((1000000 / 1711371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (38831661 / 31250000) ≤ -Real.log (288629 / 1000000) ∧
    -Real.log (288629 / 1000000) ≤ (621306577 / 500000000) := by
  have h := checkLog_sound (w := (211371 / 788629)) (n := 12)
    (lo := (137366493 / 250000000)) (hi := (549465973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 288629) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 288629) = 1/(288629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-621306577 / 500000000) (-38831661 / 31250000) (Real.log (288629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (269323011 / 500000000) ≤ -Real.log (200000 / 342737) ∧
    -Real.log (200000 / 342737) ≤ (538646023 / 1000000000) := by
  have h := checkLog_sound (w := (142737 / 542737)) (n := 12)
    (lo := (269323011 / 500000000)) (hi := (538646023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342737 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342737 / 200000) = 1/(200000 / 342737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (269323011 / 500000000) (538646023 / 1000000000) (Real.log (342737 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (342737 / 200000) = -Real.log (200000 / 342737) := by
    rw [show ((342737 / 200000) : ℝ) = ((200000 / 342737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50026507 / 40000000) ≤ -Real.log (57263 / 200000) ∧
    -Real.log (57263 / 200000) ≤ (1250662677 / 1000000000) := by
  have h := checkLog_sound (w := (42737 / 157263)) (n := 12)
    (lo := (111503099 / 200000000)) (hi := (69689437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 57263) = 1/(57263 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1250662677 / 1000000000) (-50026507 / 40000000) (Real.log (57263 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (57455093 / 125000000) ≤ -Real.log (200000 / 316701) ∧
    -Real.log (200000 / 316701) ≤ (91928149 / 200000000) := by
  have h := checkLog_sound (w := (116701 / 516701)) (n := 12)
    (lo := (57455093 / 125000000)) (hi := (91928149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316701 / 200000) = 1/(200000 / 316701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (57455093 / 125000000) (91928149 / 200000000) (Real.log (316701 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (316701 / 200000) = -Real.log (200000 / 316701) := by
    rw [show ((316701 / 200000) : ℝ) = ((200000 / 316701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (875880821 / 1000000000) ≤ -Real.log (83299 / 200000) ∧
    -Real.log (83299 / 200000) ≤ (875880823 / 1000000000) := by
  have h := checkLog_sound (w := (16701 / 183299)) (n := 12)
    (lo := (182733641 / 1000000000)) (hi := (91366821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83299) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 83299) = 1/(83299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-875880823 / 1000000000) (-875880821 / 1000000000) (Real.log (83299 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (115301889 / 250000000) ≤ -Real.log (250000 / 396497) ∧
    -Real.log (250000 / 396497) ≤ (461207557 / 1000000000) := by
  have h := checkLog_sound (w := (146497 / 646497)) (n := 12)
    (lo := (115301889 / 250000000)) (hi := (461207557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396497 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396497 / 250000) = 1/(250000 / 396497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (115301889 / 250000000) (461207557 / 1000000000) (Real.log (396497 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (396497 / 250000) = -Real.log (250000 / 396497) := by
    rw [show ((396497 / 250000) : ℝ) = ((250000 / 396497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (881860319 / 1000000000) ≤ -Real.log (103503 / 250000) ∧
    -Real.log (103503 / 250000) ≤ (881860321 / 1000000000) := by
  have h := checkLog_sound (w := (21497 / 228503)) (n := 12)
    (lo := (188713139 / 1000000000)) (hi := (9435657 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 103503) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 103503) = 1/(103503 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-881860321 / 1000000000) (-881860319 / 1000000000) (Real.log (103503 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (355981591 / 200000000) ≤ -Real.log (100000000000 / 592931063753) ∧
    -Real.log (100000000000 / 592931063753) ≤ (889953979 / 500000000) := by
  have h := checkLog_sound (w := (192931063753 / 992931063753)) (n := 12)
    (lo := (78722719 / 200000000)) (hi := (98403399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592931063753 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(592931063753 / 400000000000) = 1/(100000000000 / 592931063753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (355981591 / 200000000) (889953979 / 500000000) (Real.log (592931063753 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (592931063753 / 100000000000) = -Real.log (100000000000 / 592931063753) := by
    rw [show ((592931063753 / 100000000000) : ℝ) = ((100000000000 / 592931063753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1789308697 / 1000000000) ≤ -Real.log (500000000000 / 2992656689311) ∧
    -Real.log (500000000000 / 2992656689311) ≤ (17893087 / 10000000) := by
  have h := checkLog_sound (w := (992656689311 / 4992656689311)) (n := 12)
    (lo := (403014337 / 1000000000)) (hi := (201507169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2992656689311 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2992656689311 / 2000000000000) = 1/(500000000000 / 2992656689311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1789308697 / 1000000000) (17893087 / 10000000) (Real.log (2992656689311 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2992656689311 / 500000000000) = -Real.log (500000000000 / 2992656689311) := by
    rw [show ((2992656689311 / 500000000000) : ℝ) = ((500000000000 / 2992656689311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (667760783 / 500000000) ≤ -Real.log (500000000000 / 1900989207553) ∧
    -Real.log (500000000000 / 1900989207553) ≤ (41735049 / 31250000) := by
  have h := checkLog_sound (w := (900989207553 / 2900989207553)) (n := 12)
    (lo := (321187193 / 500000000)) (hi := (642374387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1900989207553 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1900989207553 / 1000000000000) = 1/(500000000000 / 1900989207553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (667760783 / 500000000) (41735049 / 31250000) (Real.log (1900989207553 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1900989207553 / 500000000000) = -Real.log (500000000000 / 1900989207553) := by
    rw [show ((1900989207553 / 500000000000) : ℝ) = ((500000000000 / 1900989207553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (335766969 / 250000000) ≤ -Real.log (20000000000 / 76615557037) ∧
    -Real.log (20000000000 / 76615557037) ≤ (671533939 / 500000000) := by
  have h := checkLog_sound (w := (36615557037 / 116615557037)) (n := 12)
    (lo := (81240087 / 125000000)) (hi := (649920697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76615557037 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76615557037 / 40000000000) = 1/(20000000000 / 76615557037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (335766969 / 250000000) (671533939 / 500000000) (Real.log (76615557037 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76615557037 / 20000000000) = -Real.log (20000000000 / 76615557037) := by
    rw [show ((76615557037 / 20000000000) : ℝ) = ((20000000000 / 76615557037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0035

end


