-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0226Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0226Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:33:20.479085+00:00
-- url     : https://prove2.me/theorems/2a3bfafa-74d3-4f4f-ad0f-bab4c7f20d3f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0226Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0227Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0226Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0227Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0228Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0229Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0230Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0231Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0232Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0226Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0227Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0228Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0229Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0230Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0231Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0232Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0226Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0227Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0228Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0229Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0230Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0231Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0232Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0226Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0227Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0228Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0229Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0230Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0231Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0232Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0226Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0226
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

theorem reflection_log_1_neg : (253915209 / 1000000000) ≤ -Real.log (128 / 165) ∧
    -Real.log (128 / 165) ≤ (25391521 / 100000000) := by
  have h := checkLog_sound (w := (37 / 293)) (n := 12)
    (lo := (253915209 / 1000000000)) (hi := (25391521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165 / 128) = 1/(128 / 165) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253915209 / 1000000000) (25391521 / 100000000) (Real.log (165 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (165 / 128) = -Real.log (128 / 165) := by
    rw [show ((165 / 128) : ℝ) = ((128 / 165) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (341170757 / 1000000000) ≤ -Real.log (91 / 128) ∧
    -Real.log (91 / 128) ≤ (170585379 / 500000000) := by
  have h := checkLog_sound (w := (37 / 219)) (n := 12)
    (lo := (341170757 / 1000000000)) (hi := (170585379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 91) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 91) = 1/(91 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170585379 / 500000000) (-341170757 / 1000000000) (Real.log (91 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253460561 / 1000000000) ≤ -Real.log (5120 / 6597) ∧
    -Real.log (5120 / 6597) ≤ (126730281 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 11717)) (n := 12)
    (lo := (253460561 / 1000000000)) (hi := (126730281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6597 / 5120) = 1/(5120 / 6597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253460561 / 1000000000) (126730281 / 500000000) (Real.log (6597 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6597 / 5120) = -Real.log (5120 / 6597) := by
    rw [show ((6597 / 5120) : ℝ) = ((5120 / 6597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (340346921 / 1000000000) ≤ -Real.log (3643 / 5120) ∧
    -Real.log (3643 / 5120) ≤ (170173461 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 8763)) (n := 12)
    (lo := (340346921 / 1000000000)) (hi := (170173461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3643) = 1/(3643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170173461 / 500000000) (-340346921 / 1000000000) (Real.log (3643 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (456237433 / 1000000000) ≤ -Real.log (64 / 101) ∧
    -Real.log (64 / 101) ≤ (228118717 / 500000000) := by
  have h := checkLog_sound (w := (37 / 165)) (n := 12)
    (lo := (456237433 / 1000000000)) (hi := (228118717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101 / 64) = 1/(64 / 101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (456237433 / 1000000000) (228118717 / 500000000) (Real.log (101 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (101 / 64) = -Real.log (64 / 101) := by
    rw [show ((101 / 64) : ℝ) = ((64 / 101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (107880777 / 125000000) ≤ -Real.log (27 / 64) ∧
    -Real.log (27 / 64) ≤ (431523109 / 500000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 27) = 1/(27 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-431523109 / 500000000) (-107880777 / 125000000) (Real.log (27 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (455494583 / 1000000000) ≤ -Real.log (2560 / 4037) ∧
    -Real.log (2560 / 4037) ≤ (56936823 / 125000000) := by
  have h := checkLog_sound (w := (1477 / 6597)) (n := 12)
    (lo := (455494583 / 1000000000)) (hi := (56936823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4037 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4037 / 2560) = 1/(2560 / 4037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (455494583 / 1000000000) (56936823 / 125000000) (Real.log (4037 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4037 / 2560) = -Real.log (2560 / 4037) := by
    rw [show ((4037 / 2560) : ℝ) = ((2560 / 4037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (860272289 / 1000000000) ≤ -Real.log (1083 / 2560) ∧
    -Real.log (1083 / 2560) ≤ (860272291 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2363)) (n := 12)
    (lo := (167125109 / 1000000000)) (hi := (16712511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1083) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1083) = 1/(1083 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-860272291 / 1000000000) (-860272289 / 1000000000) (Real.log (1083 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (86709227 / 250000000) ≤ -Real.log (500000 / 707293) ∧
    -Real.log (500000 / 707293) ≤ (346836909 / 1000000000) := by
  have h := checkLog_sound (w := (207293 / 1207293)) (n := 12)
    (lo := (86709227 / 250000000)) (hi := (346836909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707293 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707293 / 500000) = 1/(500000 / 707293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (86709227 / 250000000) (346836909 / 1000000000) (Real.log (707293 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (707293 / 500000) = -Real.log (500000 / 707293) := by
    rw [show ((707293 / 500000) : ℝ) = ((500000 / 707293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (535435989 / 1000000000) ≤ -Real.log (292707 / 500000) ∧
    -Real.log (292707 / 500000) ≤ (53543599 / 100000000) := by
  have h := checkLog_sound (w := (207293 / 792707)) (n := 12)
    (lo := (535435989 / 1000000000)) (hi := (53543599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 292707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 292707) = 1/(292707 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-53543599 / 100000000) (-535435989 / 1000000000) (Real.log (292707 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (347455273 / 1000000000) ≤ -Real.log (1000000 / 1415461) ∧
    -Real.log (1000000 / 1415461) ≤ (173727637 / 500000000) := by
  have h := checkLog_sound (w := (415461 / 2415461)) (n := 12)
    (lo := (347455273 / 1000000000)) (hi := (173727637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415461 / 1000000) = 1/(1000000 / 1415461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (347455273 / 1000000000) (173727637 / 500000000) (Real.log (1415461 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1415461 / 1000000) = -Real.log (1000000 / 1415461) := by
    rw [show ((1415461 / 1000000) : ℝ) = ((1000000 / 1415461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (8389559 / 15625000) ≤ -Real.log (584539 / 1000000) ∧
    -Real.log (584539 / 1000000) ≤ (536931777 / 1000000000) := by
  have h := checkLog_sound (w := (415461 / 1584539)) (n := 12)
    (lo := (8389559 / 15625000)) (hi := (536931777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 584539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 584539) = 1/(584539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-536931777 / 1000000000) (-8389559 / 15625000) (Real.log (584539 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (268328749 / 1000000000) ≤ -Real.log (1000000 / 1307777) ∧
    -Real.log (1000000 / 1307777) ≤ (214663 / 800000) := by
  have h := checkLog_sound (w := (307777 / 2307777)) (n := 12)
    (lo := (268328749 / 1000000000)) (hi := (214663 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307777 / 1000000) = 1/(1000000 / 1307777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (268328749 / 1000000000) (214663 / 800000) (Real.log (1307777 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1307777 / 1000000) = -Real.log (1000000 / 1307777) := by
    rw [show ((1307777 / 1000000) : ℝ) = ((1000000 / 1307777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4598089 / 12500000) ≤ -Real.log (692223 / 1000000) ∧
    -Real.log (692223 / 1000000) ≤ (367847121 / 1000000000) := by
  have h := checkLog_sound (w := (307777 / 1692223)) (n := 12)
    (lo := (4598089 / 12500000)) (hi := (367847121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 692223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 692223) = 1/(692223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-367847121 / 1000000000) (-4598089 / 12500000) (Real.log (692223 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67218641 / 250000000) ≤ -Real.log (1000000 / 1308491) ∧
    -Real.log (1000000 / 1308491) ≤ (53774913 / 200000000) := by
  have h := checkLog_sound (w := (308491 / 2308491)) (n := 12)
    (lo := (67218641 / 250000000)) (hi := (53774913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1308491 / 1000000) = 1/(1000000 / 1308491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67218641 / 250000000) (53774913 / 200000000) (Real.log (1308491 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1308491 / 1000000) = -Real.log (1000000 / 1308491) := by
    rw [show ((1308491 / 1000000) : ℝ) = ((1000000 / 1308491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (46109889 / 125000000) ≤ -Real.log (691509 / 1000000) ∧
    -Real.log (691509 / 1000000) ≤ (368879113 / 1000000000) := by
  have h := checkLog_sound (w := (308491 / 1691509)) (n := 12)
    (lo := (46109889 / 125000000)) (hi := (368879113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 691509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 691509) = 1/(691509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-368879113 / 1000000000) (-46109889 / 125000000) (Real.log (691509 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (882272897 / 1000000000) ≤ -Real.log (62500000000 / 151024104309) ∧
    -Real.log (62500000000 / 151024104309) ≤ (882272899 / 1000000000) := by
  have h := checkLog_sound (w := (26024104309 / 276024104309)) (n := 12)
    (lo := (189125717 / 1000000000)) (hi := (94562859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151024104309 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(151024104309 / 125000000000) = 1/(62500000000 / 151024104309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (882272897 / 1000000000) (882272899 / 1000000000) (Real.log (151024104309 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (151024104309 / 62500000000) = -Real.log (62500000000 / 151024104309) := by
    rw [show ((151024104309 / 62500000000) : ℝ) = ((62500000000 / 151024104309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (884387049 / 1000000000) ≤ -Real.log (250000000000 / 605374919381) ∧
    -Real.log (250000000000 / 605374919381) ≤ (884387051 / 1000000000) := by
  have h := checkLog_sound (w := (105374919381 / 1105374919381)) (n := 12)
    (lo := (191239869 / 1000000000)) (hi := (19123987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605374919381 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(605374919381 / 500000000000) = 1/(250000000000 / 605374919381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (884387049 / 1000000000) (884387051 / 1000000000) (Real.log (605374919381 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (605374919381 / 250000000000) = -Real.log (250000000000 / 605374919381) := by
    rw [show ((605374919381 / 250000000000) : ℝ) = ((250000000000 / 605374919381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (63617587 / 100000000) ≤ -Real.log (500000000000 / 944621169767) ∧
    -Real.log (500000000000 / 944621169767) ≤ (636175871 / 1000000000) := by
  have h := checkLog_sound (w := (444621169767 / 1444621169767)) (n := 12)
    (lo := (63617587 / 100000000)) (hi := (636175871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((944621169767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(944621169767 / 500000000000) = 1/(500000000000 / 944621169767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (63617587 / 100000000) (636175871 / 1000000000) (Real.log (944621169767 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (944621169767 / 500000000000) = -Real.log (500000000000 / 944621169767) := by
    rw [show ((944621169767 / 500000000000) : ℝ) = ((500000000000 / 944621169767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (637753677 / 1000000000) ≤ -Real.log (500000000000 / 946112776551) ∧
    -Real.log (500000000000 / 946112776551) ≤ (318876839 / 500000000) := by
  have h := checkLog_sound (w := (446112776551 / 1446112776551)) (n := 12)
    (lo := (637753677 / 1000000000)) (hi := (318876839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((946112776551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(946112776551 / 500000000000) = 1/(500000000000 / 946112776551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (637753677 / 1000000000) (318876839 / 500000000) (Real.log (946112776551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (946112776551 / 500000000000) = -Real.log (500000000000 / 946112776551) := by
    rw [show ((946112776551 / 500000000000) : ℝ) = ((500000000000 / 946112776551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0226

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0227Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0227
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

theorem reflection_log_1_neg : (253460561 / 1000000000) ≤ -Real.log (5120 / 6597) ∧
    -Real.log (5120 / 6597) ≤ (126730281 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 11717)) (n := 12)
    (lo := (253460561 / 1000000000)) (hi := (126730281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6597 / 5120) = 1/(5120 / 6597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253460561 / 1000000000) (126730281 / 500000000) (Real.log (6597 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6597 / 5120) = -Real.log (5120 / 6597) := by
    rw [show ((6597 / 5120) : ℝ) = ((5120 / 6597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (340346921 / 1000000000) ≤ -Real.log (3643 / 5120) ∧
    -Real.log (3643 / 5120) ≤ (170173461 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 8763)) (n := 12)
    (lo := (340346921 / 1000000000)) (hi := (170173461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3643) = 1/(3643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170173461 / 500000000) (-340346921 / 1000000000) (Real.log (3643 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50601141 / 200000000) ≤ -Real.log (2560 / 3297) ∧
    -Real.log (2560 / 3297) ≤ (126502853 / 500000000) := by
  have h := checkLog_sound (w := (737 / 5857)) (n := 12)
    (lo := (50601141 / 200000000)) (hi := (126502853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3297 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3297 / 2560) = 1/(2560 / 3297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50601141 / 200000000) (126502853 / 500000000) (Real.log (3297 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3297 / 2560) = -Real.log (2560 / 3297) := by
    rw [show ((3297 / 2560) : ℝ) = ((2560 / 3297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (169761881 / 500000000) ≤ -Real.log (1823 / 2560) ∧
    -Real.log (1823 / 2560) ≤ (339523763 / 1000000000) := by
  have h := checkLog_sound (w := (737 / 4383)) (n := 12)
    (lo := (169761881 / 500000000)) (hi := (339523763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1823) = 1/(1823 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-339523763 / 1000000000) (-169761881 / 500000000) (Real.log (1823 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (455494583 / 1000000000) ≤ -Real.log (2560 / 4037) ∧
    -Real.log (2560 / 4037) ≤ (56936823 / 125000000) := by
  have h := checkLog_sound (w := (1477 / 6597)) (n := 12)
    (lo := (455494583 / 1000000000)) (hi := (56936823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4037 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4037 / 2560) = 1/(2560 / 4037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (455494583 / 1000000000) (56936823 / 125000000) (Real.log (4037 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4037 / 2560) = -Real.log (2560 / 4037) := by
    rw [show ((4037 / 2560) : ℝ) = ((2560 / 4037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (860272289 / 1000000000) ≤ -Real.log (1083 / 2560) ∧
    -Real.log (1083 / 2560) ≤ (860272291 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2363)) (n := 12)
    (lo := (167125109 / 1000000000)) (hi := (16712511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1083) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1083) = 1/(1083 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-860272291 / 1000000000) (-860272289 / 1000000000) (Real.log (1083 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (454751181 / 1000000000) ≤ -Real.log (1280 / 2017) ∧
    -Real.log (1280 / 2017) ≤ (227375591 / 500000000) := by
  have h := checkLog_sound (w := (737 / 3297)) (n := 12)
    (lo := (454751181 / 1000000000)) (hi := (227375591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2017 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2017 / 1280) = 1/(1280 / 2017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (454751181 / 1000000000) (227375591 / 500000000) (Real.log (2017 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2017 / 1280) = -Real.log (1280 / 2017) := by
    rw [show ((2017 / 1280) : ℝ) = ((1280 / 2017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (214376509 / 250000000) ≤ -Real.log (543 / 1280) ∧
    -Real.log (543 / 1280) ≤ (428753019 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1183)) (n := 12)
    (lo := (20544857 / 125000000)) (hi := (164358857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 543) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 543) = 1/(543 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-428753019 / 500000000) (-214376509 / 250000000) (Real.log (543 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (346218869 / 1000000000) ≤ -Real.log (62500 / 88357) ∧
    -Real.log (62500 / 88357) ≤ (34621887 / 100000000) := by
  have h := checkLog_sound (w := (25857 / 150857)) (n := 12)
    (lo := (346218869 / 1000000000)) (hi := (34621887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88357 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88357 / 62500) = 1/(62500 / 88357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (346218869 / 1000000000) (34621887 / 100000000) (Real.log (88357 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (88357 / 62500) = -Real.log (62500 / 88357) := by
    rw [show ((88357 / 62500) : ℝ) = ((62500 / 88357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (266972071 / 500000000) ≤ -Real.log (36643 / 62500) ∧
    -Real.log (36643 / 62500) ≤ (533944143 / 1000000000) := by
  have h := checkLog_sound (w := (25857 / 99143)) (n := 12)
    (lo := (266972071 / 500000000)) (hi := (533944143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 36643) = 1/(36643 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-533944143 / 1000000000) (-266972071 / 500000000) (Real.log (36643 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (69367523 / 200000000) ≤ -Real.log (1000000 / 1414587) ∧
    -Real.log (1000000 / 1414587) ≤ (21677351 / 62500000) := by
  have h := checkLog_sound (w := (414587 / 2414587)) (n := 12)
    (lo := (69367523 / 200000000)) (hi := (21677351 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1414587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1414587 / 1000000) = 1/(1000000 / 1414587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (69367523 / 200000000) (21677351 / 62500000) (Real.log (1414587 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1414587 / 1000000) = -Real.log (1000000 / 1414587) := by
    rw [show ((1414587 / 1000000) : ℝ) = ((1000000 / 1414587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (535437697 / 1000000000) ≤ -Real.log (585413 / 1000000) ∧
    -Real.log (585413 / 1000000) ≤ (267718849 / 500000000) := by
  have h := checkLog_sound (w := (414587 / 1585413)) (n := 12)
    (lo := (535437697 / 1000000000)) (hi := (267718849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 585413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 585413) = 1/(585413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-267718849 / 500000000) (-535437697 / 1000000000) (Real.log (585413 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1338917 / 5000000) ≤ -Real.log (125000 / 163383) ∧
    -Real.log (125000 / 163383) ≤ (267783401 / 1000000000) := by
  have h := checkLog_sound (w := (38383 / 288383)) (n := 12)
    (lo := (1338917 / 5000000)) (hi := (267783401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163383 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163383 / 125000) = 1/(125000 / 163383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1338917 / 5000000) (267783401 / 1000000000) (Real.log (163383 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (163383 / 125000) = -Real.log (125000 / 163383) := by
    rw [show ((163383 / 125000) : ℝ) = ((125000 / 163383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (91704409 / 250000000) ≤ -Real.log (86617 / 125000) ∧
    -Real.log (86617 / 125000) ≤ (366817637 / 1000000000) := by
  have h := checkLog_sound (w := (38383 / 211617)) (n := 12)
    (lo := (91704409 / 250000000)) (hi := (366817637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 86617) = 1/(86617 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-366817637 / 1000000000) (-91704409 / 250000000) (Real.log (86617 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (268329513 / 1000000000) ≤ -Real.log (500000 / 653889) ∧
    -Real.log (500000 / 653889) ≤ (134164757 / 500000000) := by
  have h := checkLog_sound (w := (153889 / 1153889)) (n := 12)
    (lo := (268329513 / 1000000000)) (hi := (134164757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653889 / 500000) = 1/(500000 / 653889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (268329513 / 1000000000) (134164757 / 500000000) (Real.log (653889 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (653889 / 500000) = -Real.log (500000 / 653889) := by
    rw [show ((653889 / 500000) : ℝ) = ((500000 / 653889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73569713 / 200000000) ≤ -Real.log (346111 / 500000) ∧
    -Real.log (346111 / 500000) ≤ (183924283 / 500000000) := by
  have h := checkLog_sound (w := (153889 / 846111)) (n := 12)
    (lo := (73569713 / 200000000)) (hi := (183924283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 346111) = 1/(346111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-183924283 / 500000000) (-73569713 / 200000000) (Real.log (346111 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (880163011 / 1000000000) ≤ -Real.log (500000000000 / 1205646371749) ∧
    -Real.log (500000000000 / 1205646371749) ≤ (880163013 / 1000000000) := by
  have h := checkLog_sound (w := (205646371749 / 2205646371749)) (n := 12)
    (lo := (187015831 / 1000000000)) (hi := (23376979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205646371749 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1205646371749 / 1000000000000) = 1/(500000000000 / 1205646371749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (880163011 / 1000000000) (880163013 / 1000000000) (Real.log (1205646371749 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1205646371749 / 500000000000) = -Real.log (500000000000 / 1205646371749) := by
    rw [show ((1205646371749 / 500000000000) : ℝ) = ((500000000000 / 1205646371749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (882275313 / 1000000000) ≤ -Real.log (500000000000 / 1208195752401) ∧
    -Real.log (500000000000 / 1208195752401) ≤ (176455063 / 200000000) := by
  have h := checkLog_sound (w := (208195752401 / 2208195752401)) (n := 12)
    (lo := (189128133 / 1000000000)) (hi := (94564067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208195752401 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1208195752401 / 1000000000000) = 1/(500000000000 / 1208195752401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (882275313 / 1000000000) (176455063 / 200000000) (Real.log (1208195752401 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1208195752401 / 500000000000) = -Real.log (500000000000 / 1208195752401) := by
    rw [show ((1208195752401 / 500000000000) : ℝ) = ((500000000000 / 1208195752401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (158650259 / 250000000) ≤ -Real.log (62500000000 / 117891839939) ∧
    -Real.log (62500000000 / 117891839939) ≤ (634601037 / 1000000000) := by
  have h := checkLog_sound (w := (55391839939 / 180391839939)) (n := 12)
    (lo := (158650259 / 250000000)) (hi := (634601037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117891839939 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117891839939 / 62500000000) = 1/(62500000000 / 117891839939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (158650259 / 250000000) (634601037 / 1000000000) (Real.log (117891839939 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (117891839939 / 62500000000) = -Real.log (62500000000 / 117891839939) := by
    rw [show ((117891839939 / 62500000000) : ℝ) = ((62500000000 / 117891839939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (636178079 / 1000000000) ≤ -Real.log (500000000000 / 944623256701) ∧
    -Real.log (500000000000 / 944623256701) ≤ (3976113 / 6250000) := by
  have h := checkLog_sound (w := (444623256701 / 1444623256701)) (n := 12)
    (lo := (636178079 / 1000000000)) (hi := (3976113 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((944623256701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(944623256701 / 500000000000) = 1/(500000000000 / 944623256701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (636178079 / 1000000000) (3976113 / 6250000) (Real.log (944623256701 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (944623256701 / 500000000000) = -Real.log (500000000000 / 944623256701) := by
    rw [show ((944623256701 / 500000000000) : ℝ) = ((500000000000 / 944623256701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0227

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0228Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0228
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

theorem reflection_log_1_neg : (50601141 / 200000000) ≤ -Real.log (2560 / 3297) ∧
    -Real.log (2560 / 3297) ≤ (126502853 / 500000000) := by
  have h := checkLog_sound (w := (737 / 5857)) (n := 12)
    (lo := (50601141 / 200000000)) (hi := (126502853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3297 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3297 / 2560) = 1/(2560 / 3297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50601141 / 200000000) (126502853 / 500000000) (Real.log (3297 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3297 / 2560) = -Real.log (2560 / 3297) := by
    rw [show ((3297 / 2560) : ℝ) = ((2560 / 3297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (169761881 / 500000000) ≤ -Real.log (1823 / 2560) ∧
    -Real.log (1823 / 2560) ≤ (339523763 / 1000000000) := by
  have h := checkLog_sound (w := (737 / 4383)) (n := 12)
    (lo := (169761881 / 500000000)) (hi := (339523763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1823) = 1/(1823 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-339523763 / 1000000000) (-169761881 / 500000000) (Real.log (1823 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (252550643 / 1000000000) ≤ -Real.log (5120 / 6591) ∧
    -Real.log (5120 / 6591) ≤ (63137661 / 250000000) := by
  have h := checkLog_sound (w := (1471 / 11711)) (n := 12)
    (lo := (252550643 / 1000000000)) (hi := (63137661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6591 / 5120) = 1/(5120 / 6591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (252550643 / 1000000000) (63137661 / 250000000) (Real.log (6591 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6591 / 5120) = -Real.log (5120 / 6591) := by
    rw [show ((6591 / 5120) : ℝ) = ((5120 / 6591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (338701281 / 1000000000) ≤ -Real.log (3649 / 5120) ∧
    -Real.log (3649 / 5120) ≤ (169350641 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 8769)) (n := 12)
    (lo := (338701281 / 1000000000)) (hi := (169350641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3649) = 1/(3649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-169350641 / 500000000) (-338701281 / 1000000000) (Real.log (3649 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (454751181 / 1000000000) ≤ -Real.log (1280 / 2017) ∧
    -Real.log (1280 / 2017) ≤ (227375591 / 500000000) := by
  have h := checkLog_sound (w := (737 / 3297)) (n := 12)
    (lo := (454751181 / 1000000000)) (hi := (227375591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2017 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2017 / 1280) = 1/(1280 / 2017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (454751181 / 1000000000) (227375591 / 500000000) (Real.log (2017 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2017 / 1280) = -Real.log (1280 / 2017) := by
    rw [show ((2017 / 1280) : ℝ) = ((1280 / 2017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214376509 / 250000000) ≤ -Real.log (543 / 1280) ∧
    -Real.log (543 / 1280) ≤ (428753019 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1183)) (n := 12)
    (lo := (20544857 / 125000000)) (hi := (164358857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 543) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 543) = 1/(543 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-428753019 / 500000000) (-214376509 / 250000000) (Real.log (543 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18160289 / 40000000) ≤ -Real.log (2560 / 4031) ∧
    -Real.log (2560 / 4031) ≤ (227003613 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 6591)) (n := 12)
    (lo := (18160289 / 40000000)) (hi := (227003613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4031 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4031 / 2560) = 1/(2560 / 4031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18160289 / 40000000) (227003613 / 500000000) (Real.log (4031 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4031 / 2560) = -Real.log (2560 / 4031) := by
    rw [show ((4031 / 2560) : ℝ) = ((2560 / 4031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (854747413 / 1000000000) ≤ -Real.log (1089 / 2560) ∧
    -Real.log (1089 / 2560) ≤ (170949483 / 200000000) := by
  have h := checkLog_sound (w := (191 / 2369)) (n := 12)
    (lo := (161600233 / 1000000000)) (hi := (80800117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1089) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1089) = 1/(1089 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-170949483 / 200000000) (-854747413 / 1000000000) (Real.log (1089 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (345600447 / 1000000000) ≤ -Real.log (500000 / 706419) ∧
    -Real.log (500000 / 706419) ≤ (5400007 / 15625000) := by
  have h := checkLog_sound (w := (206419 / 1206419)) (n := 12)
    (lo := (345600447 / 1000000000)) (hi := (5400007 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706419 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706419 / 500000) = 1/(500000 / 706419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (345600447 / 1000000000) (5400007 / 15625000) (Real.log (706419 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (706419 / 500000) = -Real.log (500000 / 706419) := by
    rw [show ((706419 / 500000) : ℝ) = ((500000 / 706419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (532454517 / 1000000000) ≤ -Real.log (293581 / 500000) ∧
    -Real.log (293581 / 500000) ≤ (266227259 / 500000000) := by
  have h := checkLog_sound (w := (206419 / 793581)) (n := 12)
    (lo := (532454517 / 1000000000)) (hi := (266227259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 293581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 293581) = 1/(293581 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-266227259 / 500000000) (-532454517 / 1000000000) (Real.log (293581 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43277447 / 125000000) ≤ -Real.log (1000000 / 1413713) ∧
    -Real.log (1000000 / 1413713) ≤ (346219577 / 1000000000) := by
  have h := checkLog_sound (w := (413713 / 2413713)) (n := 12)
    (lo := (43277447 / 125000000)) (hi := (346219577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413713 / 1000000) = 1/(1000000 / 1413713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43277447 / 125000000) (346219577 / 1000000000) (Real.log (1413713 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1413713 / 1000000) = -Real.log (1000000 / 1413713) := by
    rw [show ((1413713 / 1000000) : ℝ) = ((1000000 / 1413713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (66743231 / 125000000) ≤ -Real.log (586287 / 1000000) ∧
    -Real.log (586287 / 1000000) ≤ (533945849 / 1000000000) := by
  have h := checkLog_sound (w := (413713 / 1586287)) (n := 12)
    (lo := (66743231 / 125000000)) (hi := (533945849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 586287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 586287) = 1/(586287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-533945849 / 1000000000) (-66743231 / 125000000) (Real.log (586287 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (267238519 / 1000000000) ≤ -Real.log (62500 / 81647) ∧
    -Real.log (62500 / 81647) ≤ (6680963 / 25000000) := by
  have h := checkLog_sound (w := (19147 / 144147)) (n := 12)
    (lo := (267238519 / 1000000000)) (hi := (6680963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81647 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81647 / 62500) = 1/(62500 / 81647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (267238519 / 1000000000) (6680963 / 25000000) (Real.log (81647 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (81647 / 62500) = -Real.log (62500 / 81647) := by
    rw [show ((81647 / 62500) : ℝ) = ((62500 / 81647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (365790651 / 1000000000) ≤ -Real.log (43353 / 62500) ∧
    -Real.log (43353 / 62500) ≤ (91447663 / 250000000) := by
  have h := checkLog_sound (w := (19147 / 105853)) (n := 12)
    (lo := (365790651 / 1000000000)) (hi := (91447663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43353) = 1/(43353 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-91447663 / 250000000) (-365790651 / 1000000000) (Real.log (43353 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53556833 / 200000000) ≤ -Real.log (200000 / 261413) ∧
    -Real.log (200000 / 261413) ≤ (133892083 / 500000000) := by
  have h := checkLog_sound (w := (61413 / 461413)) (n := 12)
    (lo := (53556833 / 200000000)) (hi := (133892083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261413 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261413 / 200000) = 1/(200000 / 261413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53556833 / 200000000) (133892083 / 500000000) (Real.log (261413 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (261413 / 200000) = -Real.log (200000 / 261413) := by
    rw [show ((261413 / 200000) : ℝ) = ((200000 / 261413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (366819079 / 1000000000) ≤ -Real.log (138587 / 200000) ∧
    -Real.log (138587 / 200000) ≤ (9170477 / 25000000) := by
  have h := checkLog_sound (w := (61413 / 338587)) (n := 12)
    (lo := (366819079 / 1000000000)) (hi := (9170477 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138587) = 1/(138587 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9170477 / 25000000) (-366819079 / 1000000000) (Real.log (138587 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (219513741 / 250000000) ≤ -Real.log (250000000000 / 601553744963) ∧
    -Real.log (250000000000 / 601553744963) ≤ (439027483 / 500000000) := by
  have h := checkLog_sound (w := (101553744963 / 1101553744963)) (n := 12)
    (lo := (23113473 / 125000000)) (hi := (36981557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601553744963 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(601553744963 / 500000000000) = 1/(250000000000 / 601553744963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (219513741 / 250000000) (439027483 / 500000000) (Real.log (601553744963 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (601553744963 / 250000000000) = -Real.log (250000000000 / 601553744963) := by
    rw [show ((601553744963 / 250000000000) : ℝ) = ((250000000000 / 601553744963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (55010339 / 62500000) ≤ -Real.log (62500000000 / 150706160123) ∧
    -Real.log (62500000000 / 150706160123) ≤ (440082713 / 500000000) := by
  have h := checkLog_sound (w := (25706160123 / 275706160123)) (n := 12)
    (lo := (46754561 / 250000000)) (hi := (37403649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150706160123 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(150706160123 / 125000000000) = 1/(62500000000 / 150706160123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (55010339 / 62500000) (440082713 / 500000000) (Real.log (150706160123 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (150706160123 / 62500000000) = -Real.log (62500000000 / 150706160123) := by
    rw [show ((150706160123 / 62500000000) : ℝ) = ((62500000000 / 150706160123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (633029171 / 1000000000) ≤ -Real.log (100000000000 / 188330680691) ∧
    -Real.log (100000000000 / 188330680691) ≤ (158257293 / 250000000) := by
  have h := checkLog_sound (w := (88330680691 / 288330680691)) (n := 12)
    (lo := (633029171 / 1000000000)) (hi := (158257293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188330680691 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188330680691 / 100000000000) = 1/(100000000000 / 188330680691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (633029171 / 1000000000) (158257293 / 250000000) (Real.log (188330680691 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (188330680691 / 100000000000) = -Real.log (100000000000 / 188330680691) := by
    rw [show ((188330680691 / 100000000000) : ℝ) = ((100000000000 / 188330680691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (158650811 / 250000000) ≤ -Real.log (250000000000 / 471568401077) ∧
    -Real.log (250000000000 / 471568401077) ≤ (126920649 / 200000000) := by
  have h := checkLog_sound (w := (221568401077 / 721568401077)) (n := 12)
    (lo := (158650811 / 250000000)) (hi := (126920649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471568401077 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471568401077 / 250000000000) = 1/(250000000000 / 471568401077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (158650811 / 250000000) (126920649 / 200000000) (Real.log (471568401077 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (471568401077 / 250000000000) = -Real.log (250000000000 / 471568401077) := by
    rw [show ((471568401077 / 250000000000) : ℝ) = ((250000000000 / 471568401077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0228

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0229Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0229
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

theorem reflection_log_1_neg : (252550643 / 1000000000) ≤ -Real.log (5120 / 6591) ∧
    -Real.log (5120 / 6591) ≤ (63137661 / 250000000) := by
  have h := checkLog_sound (w := (1471 / 11711)) (n := 12)
    (lo := (252550643 / 1000000000)) (hi := (63137661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6591 / 5120) = 1/(5120 / 6591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (252550643 / 1000000000) (63137661 / 250000000) (Real.log (6591 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6591 / 5120) = -Real.log (5120 / 6591) := by
    rw [show ((6591 / 5120) : ℝ) = ((5120 / 6591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (338701281 / 1000000000) ≤ -Real.log (3649 / 5120) ∧
    -Real.log (3649 / 5120) ≤ (169350641 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 8769)) (n := 12)
    (lo := (338701281 / 1000000000)) (hi := (169350641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3649) = 1/(3649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-169350641 / 500000000) (-338701281 / 1000000000) (Real.log (3649 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (252095373 / 1000000000) ≤ -Real.log (1280 / 1647) ∧
    -Real.log (1280 / 1647) ≤ (126047687 / 500000000) := by
  have h := checkLog_sound (w := (367 / 2927)) (n := 12)
    (lo := (252095373 / 1000000000)) (hi := (126047687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647 / 1280) = 1/(1280 / 1647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (252095373 / 1000000000) (126047687 / 500000000) (Real.log (1647 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1647 / 1280) = -Real.log (1280 / 1647) := by
    rw [show ((1647 / 1280) : ℝ) = ((1280 / 1647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (84469869 / 250000000) ≤ -Real.log (913 / 1280) ∧
    -Real.log (913 / 1280) ≤ (337879477 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2193)) (n := 12)
    (lo := (84469869 / 250000000)) (hi := (337879477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 913) = 1/(913 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-337879477 / 1000000000) (-84469869 / 250000000) (Real.log (913 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18160289 / 40000000) ≤ -Real.log (2560 / 4031) ∧
    -Real.log (2560 / 4031) ≤ (227003613 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 6591)) (n := 12)
    (lo := (18160289 / 40000000)) (hi := (227003613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4031 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4031 / 2560) = 1/(2560 / 4031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18160289 / 40000000) (227003613 / 500000000) (Real.log (4031 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4031 / 2560) = -Real.log (2560 / 4031) := by
    rw [show ((4031 / 2560) : ℝ) = ((2560 / 4031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (854747413 / 1000000000) ≤ -Real.log (1089 / 2560) ∧
    -Real.log (1089 / 2560) ≤ (170949483 / 200000000) := by
  have h := checkLog_sound (w := (191 / 2369)) (n := 12)
    (lo := (161600233 / 1000000000)) (hi := (80800117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1089) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1089) = 1/(1089 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-170949483 / 200000000) (-854747413 / 1000000000) (Real.log (1089 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113315679 / 250000000) ≤ -Real.log (640 / 1007) ∧
    -Real.log (640 / 1007) ≤ (453262717 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1647)) (n := 12)
    (lo := (113315679 / 250000000)) (hi := (453262717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1007 / 640) = 1/(640 / 1007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113315679 / 250000000) (453262717 / 1000000000) (Real.log (1007 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1007 / 640) = -Real.log (640 / 1007) := by
    rw [show ((1007 / 640) : ℝ) = ((640 / 1007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (42599819 / 50000000) ≤ -Real.log (273 / 640) ∧
    -Real.log (273 / 640) ≤ (425998191 / 500000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 273) = 1/(273 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-425998191 / 500000000) (-42599819 / 50000000) (Real.log (273 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (344982351 / 1000000000) ≤ -Real.log (200000 / 282393) ∧
    -Real.log (200000 / 282393) ≤ (21561397 / 62500000) := by
  have h := checkLog_sound (w := (82393 / 482393)) (n := 12)
    (lo := (344982351 / 1000000000)) (hi := (21561397 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282393 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282393 / 200000) = 1/(200000 / 282393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (344982351 / 1000000000) (21561397 / 62500000) (Real.log (282393 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282393 / 200000) = -Real.log (200000 / 282393) := by
    rw [show ((282393 / 200000) : ℝ) = ((200000 / 282393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (530968809 / 1000000000) ≤ -Real.log (117607 / 200000) ∧
    -Real.log (117607 / 200000) ≤ (53096881 / 100000000) := by
  have h := checkLog_sound (w := (82393 / 317607)) (n := 12)
    (lo := (530968809 / 1000000000)) (hi := (53096881 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 117607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 117607) = 1/(117607 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-53096881 / 100000000) (-530968809 / 1000000000) (Real.log (117607 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (69120231 / 200000000) ≤ -Real.log (1000000 / 1412839) ∧
    -Real.log (1000000 / 1412839) ≤ (86400289 / 250000000) := by
  have h := checkLog_sound (w := (412839 / 2412839)) (n := 12)
    (lo := (69120231 / 200000000)) (hi := (86400289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1412839 / 1000000) = 1/(1000000 / 1412839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (69120231 / 200000000) (86400289 / 250000000) (Real.log (1412839 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1412839 / 1000000) = -Real.log (1000000 / 1412839) := by
    rw [show ((1412839 / 1000000) : ℝ) = ((1000000 / 1412839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (26622811 / 50000000) ≤ -Real.log (587161 / 1000000) ∧
    -Real.log (587161 / 1000000) ≤ (532456221 / 1000000000) := by
  have h := checkLog_sound (w := (412839 / 1587161)) (n := 12)
    (lo := (26622811 / 50000000)) (hi := (532456221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 587161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 587161) = 1/(587161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-532456221 / 1000000000) (-26622811 / 50000000) (Real.log (587161 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133346671 / 500000000) ≤ -Real.log (25000 / 32641) ∧
    -Real.log (25000 / 32641) ≤ (266693343 / 1000000000) := by
  have h := checkLog_sound (w := (7641 / 57641)) (n := 12)
    (lo := (133346671 / 500000000)) (hi := (266693343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32641 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32641 / 25000) = 1/(25000 / 32641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133346671 / 500000000) (266693343 / 1000000000) (Real.log (32641 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (32641 / 25000) = -Real.log (25000 / 32641) := by
    rw [show ((32641 / 25000) : ℝ) = ((25000 / 32641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4559559 / 12500000) ≤ -Real.log (17359 / 25000) ∧
    -Real.log (17359 / 25000) ≤ (364764721 / 1000000000) := by
  have h := checkLog_sound (w := (7641 / 42359)) (n := 12)
    (lo := (4559559 / 12500000)) (hi := (364764721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17359) = 1/(17359 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-364764721 / 1000000000) (-4559559 / 12500000) (Real.log (17359 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53447857 / 200000000) ≤ -Real.log (1000000 / 1306353) ∧
    -Real.log (1000000 / 1306353) ≤ (133619643 / 500000000) := by
  have h := checkLog_sound (w := (306353 / 2306353)) (n := 12)
    (lo := (53447857 / 200000000)) (hi := (133619643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306353 / 1000000) = 1/(1000000 / 1306353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53447857 / 200000000) (133619643 / 500000000) (Real.log (1306353 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1306353 / 1000000) = -Real.log (1000000 / 1306353) := by
    rw [show ((1306353 / 1000000) : ℝ) = ((1000000 / 1306353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (365792093 / 1000000000) ≤ -Real.log (693647 / 1000000) ∧
    -Real.log (693647 / 1000000) ≤ (182896047 / 500000000) := by
  have h := checkLog_sound (w := (306353 / 1693647)) (n := 12)
    (lo := (365792093 / 1000000000)) (hi := (182896047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693647) = 1/(693647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-182896047 / 500000000) (-365792093 / 1000000000) (Real.log (693647 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (875951159 / 1000000000) ≤ -Real.log (100000000000 / 240115809433) ∧
    -Real.log (100000000000 / 240115809433) ≤ (875951161 / 1000000000) := by
  have h := checkLog_sound (w := (40115809433 / 440115809433)) (n := 12)
    (lo := (182803979 / 1000000000)) (hi := (9140199 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240115809433 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(240115809433 / 200000000000) = 1/(100000000000 / 240115809433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (875951159 / 1000000000) (875951161 / 1000000000) (Real.log (240115809433 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (240115809433 / 100000000000) = -Real.log (100000000000 / 240115809433) := by
    rw [show ((240115809433 / 100000000000) : ℝ) = ((100000000000 / 240115809433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (7024459 / 8000000) ≤ -Real.log (500000000000 / 1203110390507) ∧
    -Real.log (500000000000 / 1203110390507) ≤ (878057377 / 1000000000) := by
  have h := checkLog_sound (w := (203110390507 / 2203110390507)) (n := 12)
    (lo := (36982039 / 200000000)) (hi := (46227549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203110390507 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1203110390507 / 1000000000000) = 1/(500000000000 / 1203110390507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (7024459 / 8000000) (878057377 / 1000000000) (Real.log (1203110390507 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1203110390507 / 500000000000) = -Real.log (500000000000 / 1203110390507) := by
    rw [show ((1203110390507 / 500000000000) : ℝ) = ((500000000000 / 1203110390507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (315729031 / 500000000) ≤ -Real.log (100000000000 / 188035025059) ∧
    -Real.log (100000000000 / 188035025059) ≤ (631458063 / 1000000000) := by
  have h := checkLog_sound (w := (88035025059 / 288035025059)) (n := 12)
    (lo := (315729031 / 500000000)) (hi := (631458063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188035025059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188035025059 / 100000000000) = 1/(100000000000 / 188035025059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (315729031 / 500000000) (631458063 / 1000000000) (Real.log (188035025059 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (188035025059 / 100000000000) = -Real.log (100000000000 / 188035025059) := by
    rw [show ((188035025059 / 100000000000) : ℝ) = ((100000000000 / 188035025059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (316515689 / 500000000) ≤ -Real.log (500000000000 / 941655481823) ∧
    -Real.log (500000000000 / 941655481823) ≤ (633031379 / 1000000000) := by
  have h := checkLog_sound (w := (441655481823 / 1441655481823)) (n := 12)
    (lo := (316515689 / 500000000)) (hi := (633031379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941655481823 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941655481823 / 500000000000) = 1/(500000000000 / 941655481823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (316515689 / 500000000) (633031379 / 1000000000) (Real.log (941655481823 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (941655481823 / 500000000000) = -Real.log (500000000000 / 941655481823) := by
    rw [show ((941655481823 / 500000000000) : ℝ) = ((500000000000 / 941655481823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0229

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0230Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0230
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

theorem reflection_log_1_neg : (252095373 / 1000000000) ≤ -Real.log (1280 / 1647) ∧
    -Real.log (1280 / 1647) ≤ (126047687 / 500000000) := by
  have h := checkLog_sound (w := (367 / 2927)) (n := 12)
    (lo := (252095373 / 1000000000)) (hi := (126047687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647 / 1280) = 1/(1280 / 1647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (252095373 / 1000000000) (126047687 / 500000000) (Real.log (1647 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1647 / 1280) = -Real.log (1280 / 1647) := by
    rw [show ((1647 / 1280) : ℝ) = ((1280 / 1647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (84469869 / 250000000) ≤ -Real.log (913 / 1280) ∧
    -Real.log (913 / 1280) ≤ (337879477 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2193)) (n := 12)
    (lo := (84469869 / 250000000)) (hi := (337879477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 913) = 1/(913 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-337879477 / 1000000000) (-84469869 / 250000000) (Real.log (913 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (31454987 / 125000000) ≤ -Real.log (1024 / 1317) ∧
    -Real.log (1024 / 1317) ≤ (251639897 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2341)) (n := 12)
    (lo := (31454987 / 125000000)) (hi := (251639897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317 / 1024) = 1/(1024 / 1317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (31454987 / 125000000) (251639897 / 1000000000) (Real.log (1317 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1317 / 1024) = -Real.log (1024 / 1317) := by
    rw [show ((1317 / 1024) : ℝ) = ((1024 / 1317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (67411669 / 200000000) ≤ -Real.log (731 / 1024) ∧
    -Real.log (731 / 1024) ≤ (168529173 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1755)) (n := 12)
    (lo := (67411669 / 200000000)) (hi := (168529173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 731) = 1/(731 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-168529173 / 500000000) (-67411669 / 200000000) (Real.log (731 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (113315679 / 250000000) ≤ -Real.log (640 / 1007) ∧
    -Real.log (640 / 1007) ≤ (453262717 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1647)) (n := 12)
    (lo := (113315679 / 250000000)) (hi := (453262717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1007 / 640) = 1/(640 / 1007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (113315679 / 250000000) (453262717 / 1000000000) (Real.log (1007 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1007 / 640) = -Real.log (640 / 1007) := by
    rw [show ((1007 / 640) : ℝ) = ((640 / 1007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (42599819 / 50000000) ≤ -Real.log (273 / 640) ∧
    -Real.log (273 / 640) ≤ (425998191 / 500000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 273) = 1/(273 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-425998191 / 500000000) (-42599819 / 50000000) (Real.log (273 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113129413 / 250000000) ≤ -Real.log (512 / 805) ∧
    -Real.log (512 / 805) ≤ (452517653 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1317)) (n := 12)
    (lo := (113129413 / 250000000)) (hi := (452517653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805 / 512) = 1/(512 / 805) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113129413 / 250000000) (452517653 / 1000000000) (Real.log (805 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (805 / 512) = -Real.log (512 / 805) := by
    rw [show ((805 / 512) : ℝ) = ((512 / 805) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (424626447 / 500000000) ≤ -Real.log (219 / 512) ∧
    -Real.log (219 / 512) ≤ (26539153 / 31250000) := by
  have h := checkLog_sound (w := (37 / 475)) (n := 12)
    (lo := (78052857 / 500000000)) (hi := (31221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 219) = 1/(219 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26539153 / 31250000) (-424626447 / 500000000) (Real.log (219 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10761371 / 31250000) ≤ -Real.log (250000 / 352773) ∧
    -Real.log (250000 / 352773) ≤ (344363873 / 1000000000) := by
  have h := checkLog_sound (w := (102773 / 602773)) (n := 12)
    (lo := (10761371 / 31250000)) (hi := (344363873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352773 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352773 / 250000) = 1/(250000 / 352773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10761371 / 31250000) (344363873 / 1000000000) (Real.log (352773 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (352773 / 250000) = -Real.log (250000 / 352773) := by
    rw [show ((352773 / 250000) : ℝ) = ((250000 / 352773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (66185663 / 125000000) ≤ -Real.log (147227 / 250000) ∧
    -Real.log (147227 / 250000) ≤ (105897061 / 200000000) := by
  have h := checkLog_sound (w := (102773 / 397227)) (n := 12)
    (lo := (66185663 / 125000000)) (hi := (105897061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147227) = 1/(147227 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-105897061 / 200000000) (-66185663 / 125000000) (Real.log (147227 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (344983059 / 1000000000) ≤ -Real.log (500000 / 705983) ∧
    -Real.log (500000 / 705983) ≤ (17249153 / 50000000) := by
  have h := checkLog_sound (w := (205983 / 1205983)) (n := 12)
    (lo := (344983059 / 1000000000)) (hi := (17249153 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705983 / 500000) = 1/(500000 / 705983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (344983059 / 1000000000) (17249153 / 50000000) (Real.log (705983 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (705983 / 500000) = -Real.log (500000 / 705983) := by
    rw [show ((705983 / 500000) : ℝ) = ((500000 / 705983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (530970509 / 1000000000) ≤ -Real.log (294017 / 500000) ∧
    -Real.log (294017 / 500000) ≤ (53097051 / 100000000) := by
  have h := checkLog_sound (w := (205983 / 794017)) (n := 12)
    (lo := (530970509 / 1000000000)) (hi := (53097051 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 294017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 294017) = 1/(294017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-53097051 / 100000000) (-530970509 / 1000000000) (Real.log (294017 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (266148633 / 1000000000) ≤ -Real.log (1000000 / 1304929) ∧
    -Real.log (1000000 / 1304929) ≤ (133074317 / 500000000) := by
  have h := checkLog_sound (w := (304929 / 2304929)) (n := 12)
    (lo := (266148633 / 1000000000)) (hi := (133074317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304929 / 1000000) = 1/(1000000 / 1304929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (266148633 / 1000000000) (133074317 / 500000000) (Real.log (1304929 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1304929 / 1000000) = -Real.log (1000000 / 1304929) := by
    rw [show ((1304929 / 1000000) : ℝ) = ((1000000 / 1304929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2273383 / 6250000) ≤ -Real.log (695071 / 1000000) ∧
    -Real.log (695071 / 1000000) ≤ (363741281 / 1000000000) := by
  have h := checkLog_sound (w := (304929 / 1695071)) (n := 12)
    (lo := (2273383 / 6250000)) (hi := (363741281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695071) = 1/(695071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-363741281 / 1000000000) (-2273383 / 6250000) (Real.log (695071 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (266694107 / 1000000000) ≤ -Real.log (1000000 / 1305641) ∧
    -Real.log (1000000 / 1305641) ≤ (66673527 / 250000000) := by
  have h := checkLog_sound (w := (305641 / 2305641)) (n := 12)
    (lo := (266694107 / 1000000000)) (hi := (66673527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305641 / 1000000) = 1/(1000000 / 1305641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266694107 / 1000000000) (66673527 / 250000000) (Real.log (1305641 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1305641 / 1000000) = -Real.log (1000000 / 1305641) := by
    rw [show ((1305641 / 1000000) : ℝ) = ((1000000 / 1305641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (364766161 / 1000000000) ≤ -Real.log (694359 / 1000000) ∧
    -Real.log (694359 / 1000000) ≤ (182383081 / 500000000) := by
  have h := checkLog_sound (w := (305641 / 1694359)) (n := 12)
    (lo := (364766161 / 1000000000)) (hi := (182383081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 694359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 694359) = 1/(694359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-182383081 / 500000000) (-364766161 / 1000000000) (Real.log (694359 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (109231147 / 125000000) ≤ -Real.log (100000000000 / 239611620151) ∧
    -Real.log (100000000000 / 239611620151) ≤ (436924589 / 500000000) := by
  have h := checkLog_sound (w := (39611620151 / 439611620151)) (n := 12)
    (lo := (45175499 / 250000000)) (hi := (180701997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239611620151 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(239611620151 / 200000000000) = 1/(100000000000 / 239611620151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (109231147 / 125000000) (436924589 / 500000000) (Real.log (239611620151 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239611620151 / 100000000000) = -Real.log (100000000000 / 239611620151) := by
    rw [show ((239611620151 / 100000000000) : ℝ) = ((100000000000 / 239611620151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (27373549 / 31250000) ≤ -Real.log (25000000000 / 60029096957) ∧
    -Real.log (25000000000 / 60029096957) ≤ (87595357 / 100000000) := by
  have h := checkLog_sound (w := (10029096957 / 110029096957)) (n := 12)
    (lo := (45701597 / 250000000)) (hi := (182806389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60029096957 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(60029096957 / 50000000000) = 1/(25000000000 / 60029096957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (27373549 / 31250000) (87595357 / 100000000) (Real.log (60029096957 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (60029096957 / 25000000000) = -Real.log (25000000000 / 60029096957) := by
    rw [show ((60029096957 / 25000000000) : ℝ) = ((25000000000 / 60029096957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (629889913 / 1000000000) ≤ -Real.log (125000000000 / 234675486389) ∧
    -Real.log (125000000000 / 234675486389) ≤ (314944957 / 500000000) := by
  have h := checkLog_sound (w := (109675486389 / 359675486389)) (n := 12)
    (lo := (629889913 / 1000000000)) (hi := (314944957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234675486389 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234675486389 / 125000000000) = 1/(125000000000 / 234675486389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (629889913 / 1000000000) (314944957 / 500000000) (Real.log (234675486389 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (234675486389 / 125000000000) = -Real.log (125000000000 / 234675486389) := by
    rw [show ((234675486389 / 125000000000) : ℝ) = ((125000000000 / 234675486389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (631460269 / 1000000000) ≤ -Real.log (500000000000 / 940177199403) ∧
    -Real.log (500000000000 / 940177199403) ≤ (63146027 / 100000000) := by
  have h := checkLog_sound (w := (440177199403 / 1440177199403)) (n := 12)
    (lo := (631460269 / 1000000000)) (hi := (63146027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940177199403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940177199403 / 500000000000) = 1/(500000000000 / 940177199403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (631460269 / 1000000000) (63146027 / 100000000) (Real.log (940177199403 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (940177199403 / 500000000000) = -Real.log (500000000000 / 940177199403) := by
    rw [show ((940177199403 / 500000000000) : ℝ) = ((500000000000 / 940177199403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0230

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0231Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0231
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

theorem reflection_log_1_neg : (31454987 / 125000000) ≤ -Real.log (1024 / 1317) ∧
    -Real.log (1024 / 1317) ≤ (251639897 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2341)) (n := 12)
    (lo := (31454987 / 125000000)) (hi := (251639897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317 / 1024) = 1/(1024 / 1317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (31454987 / 125000000) (251639897 / 1000000000) (Real.log (1317 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1317 / 1024) = -Real.log (1024 / 1317) := by
    rw [show ((1317 / 1024) : ℝ) = ((1024 / 1317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (67411669 / 200000000) ≤ -Real.log (731 / 1024) ∧
    -Real.log (731 / 1024) ≤ (168529173 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1755)) (n := 12)
    (lo := (67411669 / 200000000)) (hi := (168529173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 731) = 1/(731 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-168529173 / 500000000) (-67411669 / 200000000) (Real.log (731 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (251184211 / 1000000000) ≤ -Real.log (2560 / 3291) ∧
    -Real.log (2560 / 3291) ≤ (62796053 / 250000000) := by
  have h := checkLog_sound (w := (731 / 5851)) (n := 12)
    (lo := (251184211 / 1000000000)) (hi := (62796053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3291 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3291 / 2560) = 1/(2560 / 3291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (251184211 / 1000000000) (62796053 / 250000000) (Real.log (3291 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3291 / 2560) = -Real.log (2560 / 3291) := by
    rw [show ((3291 / 2560) : ℝ) = ((2560 / 3291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (336237889 / 1000000000) ≤ -Real.log (1829 / 2560) ∧
    -Real.log (1829 / 2560) ≤ (33623789 / 100000000) := by
  have h := checkLog_sound (w := (731 / 4389)) (n := 12)
    (lo := (336237889 / 1000000000)) (hi := (33623789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1829) = 1/(1829 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33623789 / 100000000) (-336237889 / 1000000000) (Real.log (1829 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (113129413 / 250000000) ≤ -Real.log (512 / 805) ∧
    -Real.log (512 / 805) ≤ (452517653 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1317)) (n := 12)
    (lo := (113129413 / 250000000)) (hi := (452517653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805 / 512) = 1/(512 / 805) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (113129413 / 250000000) (452517653 / 1000000000) (Real.log (805 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (805 / 512) = -Real.log (512 / 805) := by
    rw [show ((805 / 512) : ℝ) = ((512 / 805) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (424626447 / 500000000) ≤ -Real.log (219 / 512) ∧
    -Real.log (219 / 512) ≤ (26539153 / 31250000) := by
  have h := checkLog_sound (w := (37 / 475)) (n := 12)
    (lo := (78052857 / 500000000)) (hi := (31221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 219) = 1/(219 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26539153 / 31250000) (-424626447 / 500000000) (Real.log (219 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3529469 / 7812500) ≤ -Real.log (1280 / 2011) ∧
    -Real.log (1280 / 2011) ≤ (451772033 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 3291)) (n := 12)
    (lo := (3529469 / 7812500)) (hi := (451772033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2011 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2011 / 1280) = 1/(1280 / 2011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3529469 / 7812500) (451772033 / 1000000000) (Real.log (2011 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2011 / 1280) = -Real.log (1280 / 2011) := by
    rw [show ((2011 / 1280) : ℝ) = ((1280 / 2011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (423258457 / 500000000) ≤ -Real.log (549 / 1280) ∧
    -Real.log (549 / 1280) ≤ (211629229 / 250000000) := by
  have h := checkLog_sound (w := (91 / 1189)) (n := 12)
    (lo := (76684867 / 500000000)) (hi := (30673947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 549) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 549) = 1/(549 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-211629229 / 250000000) (-423258457 / 500000000) (Real.log (549 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8593643 / 25000000) ≤ -Real.log (50000 / 70511) ∧
    -Real.log (50000 / 70511) ≤ (343745721 / 1000000000) := by
  have h := checkLog_sound (w := (20511 / 120511)) (n := 12)
    (lo := (8593643 / 25000000)) (hi := (343745721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70511 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70511 / 50000) = 1/(50000 / 70511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8593643 / 25000000) (343745721 / 1000000000) (Real.log (70511 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (70511 / 50000) = -Real.log (50000 / 70511) := by
    rw [show ((70511 / 50000) : ℝ) = ((50000 / 70511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (132001423 / 250000000) ≤ -Real.log (29489 / 50000) ∧
    -Real.log (29489 / 50000) ≤ (528005693 / 1000000000) := by
  have h := checkLog_sound (w := (20511 / 79489)) (n := 12)
    (lo := (132001423 / 250000000)) (hi := (528005693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 29489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 29489) = 1/(29489 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-528005693 / 1000000000) (-132001423 / 250000000) (Real.log (29489 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (344364581 / 1000000000) ≤ -Real.log (1000000 / 1411093) ∧
    -Real.log (1000000 / 1411093) ≤ (172182291 / 500000000) := by
  have h := checkLog_sound (w := (411093 / 2411093)) (n := 12)
    (lo := (344364581 / 1000000000)) (hi := (172182291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1411093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1411093 / 1000000) = 1/(1000000 / 1411093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (344364581 / 1000000000) (172182291 / 500000000) (Real.log (1411093 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1411093 / 1000000) = -Real.log (1000000 / 1411093) := by
    rw [show ((1411093 / 1000000) : ℝ) = ((1000000 / 1411093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (264743501 / 500000000) ≤ -Real.log (588907 / 1000000) ∧
    -Real.log (588907 / 1000000) ≤ (529487003 / 1000000000) := by
  have h := checkLog_sound (w := (411093 / 1588907)) (n := 12)
    (lo := (264743501 / 500000000)) (hi := (529487003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 588907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 588907) = 1/(588907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-529487003 / 1000000000) (-264743501 / 500000000) (Real.log (588907 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132802197 / 500000000) ≤ -Real.log (1000000 / 1304219) ∧
    -Real.log (1000000 / 1304219) ≤ (53120879 / 200000000) := by
  have h := checkLog_sound (w := (304219 / 2304219)) (n := 12)
    (lo := (132802197 / 500000000)) (hi := (53120879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304219 / 1000000) = 1/(1000000 / 1304219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132802197 / 500000000) (53120879 / 200000000) (Real.log (1304219 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1304219 / 1000000) = -Real.log (1000000 / 1304219) := by
    rw [show ((1304219 / 1000000) : ℝ) = ((1000000 / 1304219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (362720323 / 1000000000) ≤ -Real.log (695781 / 1000000) ∧
    -Real.log (695781 / 1000000) ≤ (90680081 / 250000000) := by
  have h := checkLog_sound (w := (304219 / 1695781)) (n := 12)
    (lo := (362720323 / 1000000000)) (hi := (90680081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695781) = 1/(695781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-90680081 / 250000000) (-362720323 / 1000000000) (Real.log (695781 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (266149399 / 1000000000) ≤ -Real.log (100000 / 130493) ∧
    -Real.log (100000 / 130493) ≤ (1330747 / 5000000) := by
  have h := checkLog_sound (w := (30493 / 230493)) (n := 12)
    (lo := (266149399 / 1000000000)) (hi := (1330747 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130493 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130493 / 100000) = 1/(100000 / 130493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266149399 / 1000000000) (1330747 / 5000000) (Real.log (130493 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (130493 / 100000) = -Real.log (100000 / 130493) := by
    rw [show ((130493 / 100000) : ℝ) = ((100000 / 130493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (363742719 / 1000000000) ≤ -Real.log (69507 / 100000) ∧
    -Real.log (69507 / 100000) ≤ (142087 / 390625) := by
  have h := checkLog_sound (w := (30493 / 169507)) (n := 12)
    (lo := (363742719 / 1000000000)) (hi := (142087 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69507) = 1/(69507 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-142087 / 390625) (-363742719 / 1000000000) (Real.log (69507 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (871751413 / 1000000000) ≤ -Real.log (100000000000 / 239109498457) ∧
    -Real.log (100000000000 / 239109498457) ≤ (174350283 / 200000000) := by
  have h := checkLog_sound (w := (39109498457 / 439109498457)) (n := 12)
    (lo := (178604233 / 1000000000)) (hi := (89302117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239109498457 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(239109498457 / 200000000000) = 1/(100000000000 / 239109498457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (871751413 / 1000000000) (174350283 / 200000000) (Real.log (239109498457 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239109498457 / 100000000000) = -Real.log (100000000000 / 239109498457) := by
    rw [show ((239109498457 / 100000000000) : ℝ) = ((100000000000 / 239109498457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (873851583 / 1000000000) ≤ -Real.log (500000000000 / 1198060984163) ∧
    -Real.log (500000000000 / 1198060984163) ≤ (174770317 / 200000000) := by
  have h := checkLog_sound (w := (198060984163 / 2198060984163)) (n := 12)
    (lo := (180704403 / 1000000000)) (hi := (45176101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198060984163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1198060984163 / 1000000000000) = 1/(500000000000 / 1198060984163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (873851583 / 1000000000) (174770317 / 200000000) (Real.log (1198060984163 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1198060984163 / 500000000000) = -Real.log (500000000000 / 1198060984163) := by
    rw [show ((1198060984163 / 500000000000) : ℝ) = ((500000000000 / 1198060984163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (628324717 / 1000000000) ≤ -Real.log (500000000000 / 937233842257) ∧
    -Real.log (500000000000 / 937233842257) ≤ (314162359 / 500000000) := by
  have h := checkLog_sound (w := (437233842257 / 1437233842257)) (n := 12)
    (lo := (628324717 / 1000000000)) (hi := (314162359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((937233842257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(937233842257 / 500000000000) = 1/(500000000000 / 937233842257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (628324717 / 1000000000) (314162359 / 500000000) (Real.log (937233842257 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (937233842257 / 500000000000) = -Real.log (500000000000 / 937233842257) := by
    rw [show ((937233842257 / 500000000000) : ℝ) = ((500000000000 / 937233842257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (314946059 / 500000000) ≤ -Real.log (500000000000 / 938704015423) ∧
    -Real.log (500000000000 / 938704015423) ≤ (629892119 / 1000000000) := by
  have h := checkLog_sound (w := (438704015423 / 1438704015423)) (n := 12)
    (lo := (314946059 / 500000000)) (hi := (629892119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938704015423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938704015423 / 500000000000) = 1/(500000000000 / 938704015423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (314946059 / 500000000) (629892119 / 1000000000) (Real.log (938704015423 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (938704015423 / 500000000000) = -Real.log (500000000000 / 938704015423) := by
    rw [show ((938704015423 / 500000000000) : ℝ) = ((500000000000 / 938704015423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0231

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0232Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0232
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

theorem reflection_log_1_neg : (251184211 / 1000000000) ≤ -Real.log (2560 / 3291) ∧
    -Real.log (2560 / 3291) ≤ (62796053 / 250000000) := by
  have h := checkLog_sound (w := (731 / 5851)) (n := 12)
    (lo := (251184211 / 1000000000)) (hi := (62796053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3291 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3291 / 2560) = 1/(2560 / 3291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (251184211 / 1000000000) (62796053 / 250000000) (Real.log (3291 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3291 / 2560) = -Real.log (2560 / 3291) := by
    rw [show ((3291 / 2560) : ℝ) = ((2560 / 3291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (336237889 / 1000000000) ≤ -Real.log (1829 / 2560) ∧
    -Real.log (1829 / 2560) ≤ (33623789 / 100000000) := by
  have h := checkLog_sound (w := (731 / 4389)) (n := 12)
    (lo := (336237889 / 1000000000)) (hi := (33623789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1829) = 1/(1829 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33623789 / 100000000) (-336237889 / 1000000000) (Real.log (1829 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (250728319 / 1000000000) ≤ -Real.log (5120 / 6579) ∧
    -Real.log (5120 / 6579) ≤ (391763 / 1562500) := by
  have h := checkLog_sound (w := (1459 / 11699)) (n := 12)
    (lo := (250728319 / 1000000000)) (hi := (391763 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6579 / 5120) = 1/(5120 / 6579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (250728319 / 1000000000) (391763 / 1562500) (Real.log (6579 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6579 / 5120) = -Real.log (5120 / 6579) := by
    rw [show ((6579 / 5120) : ℝ) = ((5120 / 6579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41927263 / 125000000) ≤ -Real.log (3661 / 5120) ∧
    -Real.log (3661 / 5120) ≤ (67083621 / 200000000) := by
  have h := checkLog_sound (w := (1459 / 8781)) (n := 12)
    (lo := (41927263 / 125000000)) (hi := (67083621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3661) = 1/(3661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-67083621 / 200000000) (-41927263 / 125000000) (Real.log (3661 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3529469 / 7812500) ≤ -Real.log (1280 / 2011) ∧
    -Real.log (1280 / 2011) ≤ (451772033 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 3291)) (n := 12)
    (lo := (3529469 / 7812500)) (hi := (451772033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2011 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2011 / 1280) = 1/(1280 / 2011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3529469 / 7812500) (451772033 / 1000000000) (Real.log (2011 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2011 / 1280) = -Real.log (1280 / 2011) := by
    rw [show ((2011 / 1280) : ℝ) = ((1280 / 2011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (423258457 / 500000000) ≤ -Real.log (549 / 1280) ∧
    -Real.log (549 / 1280) ≤ (211629229 / 250000000) := by
  have h := checkLog_sound (w := (91 / 1189)) (n := 12)
    (lo := (76684867 / 500000000)) (hi := (30673947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 549) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 549) = 1/(549 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-211629229 / 250000000) (-423258457 / 500000000) (Real.log (549 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7047279 / 15625000) ≤ -Real.log (2560 / 4019) ∧
    -Real.log (2560 / 4019) ≤ (451025857 / 1000000000) := by
  have h := checkLog_sound (w := (1459 / 6579)) (n := 12)
    (lo := (7047279 / 15625000)) (hi := (451025857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4019 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4019 / 2560) = 1/(2560 / 4019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7047279 / 15625000) (451025857 / 1000000000) (Real.log (4019 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4019 / 2560) = -Real.log (2560 / 4019) := by
    rw [show ((4019 / 2560) : ℝ) = ((2560 / 4019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2109471 / 2500000) ≤ -Real.log (1101 / 2560) ∧
    -Real.log (1101 / 2560) ≤ (421894201 / 500000000) := by
  have h := checkLog_sound (w := (179 / 2381)) (n := 12)
    (lo := (7532061 / 50000000)) (hi := (150641221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1101) = 1/(1101 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-421894201 / 500000000) (-2109471 / 2500000) (Real.log (1101 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85781619 / 250000000) ≤ -Real.log (1000000 / 1409347) ∧
    -Real.log (1000000 / 1409347) ≤ (343126477 / 1000000000) := by
  have h := checkLog_sound (w := (409347 / 2409347)) (n := 12)
    (lo := (85781619 / 250000000)) (hi := (343126477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409347 / 1000000) = 1/(1000000 / 1409347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85781619 / 250000000) (343126477 / 1000000000) (Real.log (1409347 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1409347 / 1000000) = -Real.log (1000000 / 1409347) := by
    rw [show ((1409347 / 1000000) : ℝ) = ((1000000 / 1409347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (263263287 / 500000000) ≤ -Real.log (590653 / 1000000) ∧
    -Real.log (590653 / 1000000) ≤ (21061063 / 40000000) := by
  have h := checkLog_sound (w := (409347 / 1590653)) (n := 12)
    (lo := (263263287 / 500000000)) (hi := (21061063 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 590653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 590653) = 1/(590653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21061063 / 40000000) (-263263287 / 500000000) (Real.log (590653 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (343746429 / 1000000000) ≤ -Real.log (1000000 / 1410221) ∧
    -Real.log (1000000 / 1410221) ≤ (34374643 / 100000000) := by
  have h := checkLog_sound (w := (410221 / 2410221)) (n := 12)
    (lo := (343746429 / 1000000000)) (hi := (34374643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1410221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1410221 / 1000000) = 1/(1000000 / 1410221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (343746429 / 1000000000) (34374643 / 100000000) (Real.log (1410221 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1410221 / 1000000) = -Real.log (1000000 / 1410221) := by
    rw [show ((1410221 / 1000000) : ℝ) = ((1000000 / 1410221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (132001847 / 250000000) ≤ -Real.log (589779 / 1000000) ∧
    -Real.log (589779 / 1000000) ≤ (528007389 / 1000000000) := by
  have h := checkLog_sound (w := (410221 / 1589779)) (n := 12)
    (lo := (132001847 / 250000000)) (hi := (528007389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 589779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 589779) = 1/(589779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-528007389 / 1000000000) (-132001847 / 250000000) (Real.log (589779 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132529929 / 500000000) ≤ -Real.log (1000000 / 1303509) ∧
    -Real.log (1000000 / 1303509) ≤ (265059859 / 1000000000) := by
  have h := checkLog_sound (w := (303509 / 2303509)) (n := 12)
    (lo := (132529929 / 500000000)) (hi := (265059859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303509 / 1000000) = 1/(1000000 / 1303509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132529929 / 500000000) (265059859 / 1000000000) (Real.log (1303509 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1303509 / 1000000) = -Real.log (1000000 / 1303509) := by
    rw [show ((1303509 / 1000000) : ℝ) = ((1000000 / 1303509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (361700407 / 1000000000) ≤ -Real.log (696491 / 1000000) ∧
    -Real.log (696491 / 1000000) ≤ (45212551 / 125000000) := by
  have h := checkLog_sound (w := (303509 / 1696491)) (n := 12)
    (lo := (361700407 / 1000000000)) (hi := (45212551 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696491) = 1/(696491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45212551 / 125000000) (-361700407 / 1000000000) (Real.log (696491 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6640129 / 25000000) ≤ -Real.log (50000 / 65211) ∧
    -Real.log (50000 / 65211) ≤ (265605161 / 1000000000) := by
  have h := checkLog_sound (w := (15211 / 115211)) (n := 12)
    (lo := (6640129 / 25000000)) (hi := (265605161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65211 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65211 / 50000) = 1/(50000 / 65211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6640129 / 25000000) (265605161 / 1000000000) (Real.log (65211 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (65211 / 50000) = -Real.log (50000 / 65211) := by
    rw [show ((65211 / 50000) : ℝ) = ((50000 / 65211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2267011 / 6250000) ≤ -Real.log (34789 / 50000) ∧
    -Real.log (34789 / 50000) ≤ (362721761 / 1000000000) := by
  have h := checkLog_sound (w := (15211 / 84789)) (n := 12)
    (lo := (2267011 / 6250000)) (hi := (362721761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34789) = 1/(34789 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-362721761 / 1000000000) (-2267011 / 6250000) (Real.log (34789 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (17393061 / 20000000) ≤ -Real.log (31250000000 / 74565089401) ∧
    -Real.log (31250000000 / 74565089401) ≤ (217413263 / 250000000) := by
  have h := checkLog_sound (w := (12065089401 / 137065089401)) (n := 12)
    (lo := (17650587 / 100000000)) (hi := (176505871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74565089401 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(74565089401 / 62500000000) = 1/(31250000000 / 74565089401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (17393061 / 20000000) (217413263 / 250000000) (Real.log (74565089401 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (74565089401 / 31250000000) = -Real.log (31250000000 / 74565089401) := by
    rw [show ((74565089401 / 31250000000) : ℝ) = ((31250000000 / 74565089401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (871753817 / 1000000000) ≤ -Real.log (125000000000 / 298887591793) ∧
    -Real.log (125000000000 / 298887591793) ≤ (871753819 / 1000000000) := by
  have h := checkLog_sound (w := (48887591793 / 548887591793)) (n := 12)
    (lo := (178606637 / 1000000000)) (hi := (89303319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298887591793 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(298887591793 / 250000000000) = 1/(125000000000 / 298887591793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (871753817 / 1000000000) (871753819 / 1000000000) (Real.log (298887591793 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (298887591793 / 125000000000) = -Real.log (125000000000 / 298887591793) := by
    rw [show ((298887591793 / 125000000000) : ℝ) = ((125000000000 / 298887591793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (313380133 / 500000000) ≤ -Real.log (100000000000 / 187153746423) ∧
    -Real.log (100000000000 / 187153746423) ≤ (626760267 / 1000000000) := by
  have h := checkLog_sound (w := (87153746423 / 287153746423)) (n := 12)
    (lo := (313380133 / 500000000)) (hi := (626760267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187153746423 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187153746423 / 100000000000) = 1/(100000000000 / 187153746423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (313380133 / 500000000) (626760267 / 1000000000) (Real.log (187153746423 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (187153746423 / 100000000000) = -Real.log (100000000000 / 187153746423) := by
    rw [show ((187153746423 / 100000000000) : ℝ) = ((100000000000 / 187153746423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (628326921 / 1000000000) ≤ -Real.log (250000000000 / 468617953951) ∧
    -Real.log (250000000000 / 468617953951) ≤ (314163461 / 500000000) := by
  have h := checkLog_sound (w := (218617953951 / 718617953951)) (n := 12)
    (lo := (628326921 / 1000000000)) (hi := (314163461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468617953951 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468617953951 / 250000000000) = 1/(250000000000 / 468617953951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (628326921 / 1000000000) (314163461 / 500000000) (Real.log (468617953951 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (468617953951 / 250000000000) = -Real.log (250000000000 / 468617953951) := by
    rw [show ((468617953951 / 250000000000) : ℝ) = ((250000000000 / 468617953951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0232

end


