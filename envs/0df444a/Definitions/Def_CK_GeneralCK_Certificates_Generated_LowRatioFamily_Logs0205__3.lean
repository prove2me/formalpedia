-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0205__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0205__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T20:49:45.754004+00:00
-- url     : https://prove2.me/theorems/ca3dc0c9-442e-4e5c-86fd-f8b50159d511
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0205 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0206, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0205 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0206, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0207)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0205 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0206, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0207)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0205 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0206, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0207) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0205 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0206, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0207).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0205 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13120_neg : (120245039 / 1000000000) ≤ -Real.log (55418945799 / 62500000000) ∧
    -Real.log (55418945799 / 62500000000) ≤ (1503063 / 12500000) := by
  have h := checkLog_sound (w := (7081054201 / 117918945799)) (n := 12)
    (lo := (120245039 / 1000000000)) (hi := (1503063 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55418945799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55418945799) = 1/(55418945799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13120 : Bounds (-1503063 / 12500000) (-120245039 / 1000000000) (Real.log (55418945799 / 62500000000)) := by
  have h := reflection_log_13120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13121_neg : (59193347 / 500000000) ≤ -Real.log (888352465231 / 1000000000000) ∧
    -Real.log (888352465231 / 1000000000000) ≤ (23677339 / 200000000) := by
  have h := checkLog_sound (w := (111647534769 / 1888352465231)) (n := 12)
    (lo := (59193347 / 500000000)) (hi := (23677339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 888352465231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 888352465231) = 1/(888352465231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13121 : Bounds (-23677339 / 200000000) (-59193347 / 500000000) (Real.log (888352465231 / 1000000000000)) := by
  have h := reflection_log_13121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13122_neg : (27798239 / 40000000) ≤ -Real.log (125000000000 / 250452608119) ∧
    -Real.log (125000000000 / 250452608119) ≤ (694955977 / 1000000000) := by
  have h := checkLog_sound (w := (452608119 / 500452608119)) (n := 12)
    (lo := (361759 / 200000000)) (hi := (452199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250452608119 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250452608119 / 250000000000) = 1/(125000000000 / 250452608119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13122 : Bounds (27798239 / 40000000) (694955977 / 1000000000) (Real.log (250452608119 / 125000000000)) := by
  have h := reflection_log_13122_neg
  have he : Real.log (250452608119 / 125000000000) = -Real.log (125000000000 / 250452608119) := by
    rw [show ((250452608119 / 125000000000) : ℝ) = ((125000000000 / 250452608119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13123_neg : (140099441 / 200000000) ≤ -Real.log (100000000000 / 201475420709) ∧
    -Real.log (100000000000 / 201475420709) ≤ (700497207 / 1000000000) := by
  have h := checkLog_sound (w := (1475420709 / 401475420709)) (n := 12)
    (lo := (294001 / 40000000)) (hi := (3675013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201475420709 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(201475420709 / 200000000000) = 1/(100000000000 / 201475420709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13123 : Bounds (140099441 / 200000000) (700497207 / 1000000000) (Real.log (201475420709 / 100000000000)) := by
  have h := reflection_log_13123_neg
  have he : Real.log (201475420709 / 100000000000) = -Real.log (100000000000 / 201475420709) := by
    rw [show ((201475420709 / 100000000000) : ℝ) = ((100000000000 / 201475420709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13124_neg : (725005087 / 500000000) ≤ -Real.log (62500000000 / 266447368421) ∧
    -Real.log (62500000000 / 266447368421) ≤ (1450010177 / 1000000000) := by
  have h := checkLog_sound (w := (16447368421 / 516447368421)) (n := 12)
    (lo := (31857907 / 500000000)) (hi := (12743163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266447368421 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(266447368421 / 250000000000) = 1/(62500000000 / 266447368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13124 : Bounds (725005087 / 500000000) (1450010177 / 1000000000) (Real.log (266447368421 / 62500000000)) := by
  have h := reflection_log_13124_neg
  have he : Real.log (266447368421 / 62500000000) = -Real.log (62500000000 / 266447368421) := by
    rw [show ((266447368421 / 62500000000) : ℝ) = ((62500000000 / 266447368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13125_neg : (729893189 / 500000000) ≤ -Real.log (5000000000 / 21525198939) ∧
    -Real.log (5000000000 / 21525198939) ≤ (1459786381 / 1000000000) := by
  have h := checkLog_sound (w := (1525198939 / 41525198939)) (n := 12)
    (lo := (36746009 / 500000000)) (hi := (73492019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21525198939 / 20000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(21525198939 / 20000000000) = 1/(5000000000 / 21525198939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13125 : Bounds (729893189 / 500000000) (1459786381 / 1000000000) (Real.log (21525198939 / 5000000000)) := by
  have h := reflection_log_13125_neg
  have he : Real.log (21525198939 / 5000000000) = -Real.log (5000000000 / 21525198939) := by
    rw [show ((21525198939 / 5000000000) : ℝ) = ((5000000000 / 21525198939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13126_neg : (486123011 / 1000000000) ≤ -Real.log (500 / 813) ∧
    -Real.log (500 / 813) ≤ (121530753 / 250000000) := by
  have h := checkLog_sound (w := (313 / 1313)) (n := 12)
    (lo := (486123011 / 1000000000)) (hi := (121530753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813 / 500) = 1/(500 / 813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13126 : Bounds (486123011 / 1000000000) (121530753 / 250000000) (Real.log (813 / 500)) := by
  have h := reflection_log_13126_neg
  have he : Real.log (813 / 500) = -Real.log (500 / 813) := by
    rw [show ((813 / 500) : ℝ) = ((500 / 813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13127_neg : (983499481 / 1000000000) ≤ -Real.log (187 / 500) ∧
    -Real.log (187 / 500) ≤ (983499483 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 437)) (n := 12)
    (lo := (290352301 / 1000000000)) (hi := (145176151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 187) = 1/(187 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13127 : Bounds (-983499483 / 1000000000) (-983499481 / 1000000000) (Real.log (187 / 500)) := by
  have h := reflection_log_13127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13128_neg : (156451 / 250000000) ≤ -Real.log (500000 / 500313) ∧
    -Real.log (500000 / 500313) ≤ (125161 / 200000000) := by
  have h := checkLog_sound (w := (313 / 1000313)) (n := 12)
    (lo := (156451 / 250000000)) (hi := (125161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500313 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500313 / 500000) = 1/(500000 / 500313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13128 : Bounds (156451 / 250000000) (125161 / 200000000) (Real.log (500313 / 500000)) := by
  have h := reflection_log_13128_neg
  have he : Real.log (500313 / 500000) = -Real.log (500000 / 500313) := by
    rw [show ((500313 / 500000) : ℝ) = ((500000 / 500313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13129_neg : (156549 / 250000000) ≤ -Real.log (499687 / 500000) ∧
    -Real.log (499687 / 500000) ≤ (626197 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 999687)) (n := 12)
    (lo := (156549 / 250000000)) (hi := (626197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499687) = 1/(499687 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13129 : Bounds (-626197 / 1000000000) (-156549 / 250000000) (Real.log (499687 / 500000)) := by
  have h := reflection_log_13129_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13130_neg : (72425071 / 250000000) ≤ -Real.log (1000000 / 1336027) ∧
    -Real.log (1000000 / 1336027) ≤ (57940057 / 200000000) := by
  have h := checkLog_sound (w := (336027 / 2336027)) (n := 12)
    (lo := (72425071 / 250000000)) (hi := (57940057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1336027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1336027 / 1000000) = 1/(1000000 / 1336027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13130 : Bounds (72425071 / 250000000) (57940057 / 200000000) (Real.log (1336027 / 1000000)) := by
  have h := reflection_log_13130_neg
  have he : Real.log (1336027 / 1000000) = -Real.log (1000000 / 1336027) := by
    rw [show ((1336027 / 1000000) : ℝ) = ((1000000 / 1336027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13131_neg : (6398653 / 15625000) ≤ -Real.log (663973 / 1000000) ∧
    -Real.log (663973 / 1000000) ≤ (409513793 / 1000000000) := by
  have h := checkLog_sound (w := (336027 / 1663973)) (n := 12)
    (lo := (6398653 / 15625000)) (hi := (409513793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 663973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 663973) = 1/(663973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13131 : Bounds (-409513793 / 1000000000) (-6398653 / 15625000) (Real.log (663973 / 1000000)) := by
  have h := reflection_log_13131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13132_neg : (291545101 / 1000000000) ≤ -Real.log (500000 / 669247) ∧
    -Real.log (500000 / 669247) ≤ (145772551 / 500000000) := by
  have h := checkLog_sound (w := (169247 / 1169247)) (n := 12)
    (lo := (291545101 / 1000000000)) (hi := (145772551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669247 / 500000) = 1/(500000 / 669247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13132 : Bounds (291545101 / 1000000000) (145772551 / 500000000) (Real.log (669247 / 500000)) := by
  have h := reflection_log_13132_neg
  have he : Real.log (669247 / 500000) = -Real.log (500000 / 669247) := by
    rw [show ((669247 / 500000) : ℝ) = ((500000 / 669247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13133_neg : (16529449 / 40000000) ≤ -Real.log (330753 / 500000) ∧
    -Real.log (330753 / 500000) ≤ (206618113 / 500000000) := by
  have h := checkLog_sound (w := (169247 / 830753)) (n := 12)
    (lo := (16529449 / 40000000)) (hi := (206618113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330753) = 1/(330753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13133 : Bounds (-206618113 / 500000000) (-16529449 / 40000000) (Real.log (330753 / 500000)) := by
  have h := reflection_log_13133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13134_neg : (121691123 / 1000000000) ≤ -Real.log (221355452991 / 250000000000) ∧
    -Real.log (221355452991 / 250000000000) ≤ (30422781 / 250000000) := by
  have h := checkLog_sound (w := (28644547009 / 471355452991)) (n := 12)
    (lo := (121691123 / 1000000000)) (hi := (30422781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 221355452991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 221355452991) = 1/(221355452991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13134 : Bounds (-30422781 / 250000000) (-121691123 / 1000000000) (Real.log (221355452991 / 250000000000)) := by
  have h := reflection_log_13134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13135_neg : (29953377 / 250000000) ≤ -Real.log (887085855271 / 1000000000000) ∧
    -Real.log (887085855271 / 1000000000000) ≤ (119813509 / 1000000000) := by
  have h := checkLog_sound (w := (112914144729 / 1887085855271)) (n := 12)
    (lo := (29953377 / 250000000)) (hi := (119813509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 887085855271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 887085855271) = 1/(887085855271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13135 : Bounds (-119813509 / 1000000000) (-29953377 / 250000000) (Real.log (887085855271 / 1000000000000)) := by
  have h := reflection_log_13135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13136_neg : (174803519 / 250000000) ≤ -Real.log (500000000000 / 1006085337807) ∧
    -Real.log (500000000000 / 1006085337807) ≤ (349607039 / 500000000) := by
  have h := checkLog_sound (w := (6085337807 / 2006085337807)) (n := 12)
    (lo := (379181 / 62500000)) (hi := (6066897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006085337807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006085337807 / 1000000000000) = 1/(500000000000 / 1006085337807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13136 : Bounds (174803519 / 250000000) (349607039 / 500000000) (Real.log (1006085337807 / 500000000000)) := by
  have h := reflection_log_13136_neg
  have he : Real.log (1006085337807 / 500000000000) = -Real.log (500000000000 / 1006085337807) := by
    rw [show ((1006085337807 / 500000000000) : ℝ) = ((500000000000 / 1006085337807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13137_neg : (28191253 / 40000000) ≤ -Real.log (500000000000 / 1011702085847) ∧
    -Real.log (500000000000 / 1011702085847) ≤ (704781327 / 1000000000) := by
  have h := checkLog_sound (w := (11702085847 / 2011702085847)) (n := 12)
    (lo := (2326829 / 200000000)) (hi := (5817073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011702085847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011702085847 / 1000000000000) = 1/(500000000000 / 1011702085847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13137 : Bounds (28191253 / 40000000) (704781327 / 1000000000) (Real.log (1011702085847 / 500000000000)) := by
  have h := reflection_log_13137_neg
  have he : Real.log (1011702085847 / 500000000000) = -Real.log (500000000000 / 1011702085847) := by
    rw [show ((1011702085847 / 500000000000) : ℝ) = ((500000000000 / 1011702085847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13138_neg : (729893189 / 500000000) ≤ -Real.log (500000000000 / 2152519893899) ∧
    -Real.log (500000000000 / 2152519893899) ≤ (1459786381 / 1000000000) := by
  have h := checkLog_sound (w := (152519893899 / 4152519893899)) (n := 12)
    (lo := (36746009 / 500000000)) (hi := (73492019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2152519893899 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2152519893899 / 2000000000000) = 1/(500000000000 / 2152519893899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13138 : Bounds (729893189 / 500000000) (1459786381 / 1000000000) (Real.log (2152519893899 / 500000000000)) := by
  have h := reflection_log_13138_neg
  have he : Real.log (2152519893899 / 500000000000) = -Real.log (500000000000 / 2152519893899) := by
    rw [show ((2152519893899 / 500000000000) : ℝ) = ((500000000000 / 2152519893899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13139_neg : (1469622491 / 1000000000) ≤ -Real.log (125000000000 / 543449197861) ∧
    -Real.log (125000000000 / 543449197861) ≤ (734811247 / 500000000) := by
  have h := checkLog_sound (w := (43449197861 / 1043449197861)) (n := 12)
    (lo := (83328131 / 1000000000)) (hi := (20832033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543449197861 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(543449197861 / 500000000000) = 1/(125000000000 / 543449197861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13139 : Bounds (1469622491 / 1000000000) (734811247 / 500000000) (Real.log (543449197861 / 125000000000)) := by
  have h := reflection_log_13139_neg
  have he : Real.log (543449197861 / 125000000000) = -Real.log (125000000000 / 543449197861) := by
    rw [show ((543449197861 / 125000000000) : ℝ) = ((125000000000 / 543449197861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13140_neg : (487966329 / 1000000000) ≤ -Real.log (1000 / 1629) ∧
    -Real.log (1000 / 1629) ≤ (48796633 / 100000000) := by
  have h := checkLog_sound (w := (629 / 2629)) (n := 12)
    (lo := (487966329 / 1000000000)) (hi := (48796633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1629 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1629 / 1000) = 1/(1000 / 1629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13140 : Bounds (487966329 / 1000000000) (48796633 / 100000000) (Real.log (1629 / 1000)) := by
  have h := reflection_log_13140_neg
  have he : Real.log (1629 / 1000) = -Real.log (1000 / 1629) := by
    rw [show ((1629 / 1000) : ℝ) = ((1000 / 1629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13141_neg : (198310643 / 200000000) ≤ -Real.log (371 / 1000) ∧
    -Real.log (371 / 1000) ≤ (991553217 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 871)) (n := 12)
    (lo := (59681207 / 200000000)) (hi := (74601509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 371) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 371) = 1/(371 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13141 : Bounds (-991553217 / 1000000000) (-198310643 / 200000000) (Real.log (371 / 1000)) := by
  have h := reflection_log_13141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13142_neg : (314401 / 500000000) ≤ -Real.log (1000000 / 1000629) ∧
    -Real.log (1000000 / 1000629) ≤ (628803 / 1000000000) := by
  have h := checkLog_sound (w := (629 / 2000629)) (n := 12)
    (lo := (314401 / 500000000)) (hi := (628803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000629 / 1000000) = 1/(1000000 / 1000629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13142 : Bounds (314401 / 500000000) (628803 / 1000000000) (Real.log (1000629 / 1000000)) := by
  have h := reflection_log_13142_neg
  have he : Real.log (1000629 / 1000000) = -Real.log (1000000 / 1000629) := by
    rw [show ((1000629 / 1000000) : ℝ) = ((1000000 / 1000629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13143_neg : (629197 / 1000000000) ≤ -Real.log (999371 / 1000000) ∧
    -Real.log (999371 / 1000000) ≤ (314599 / 500000000) := by
  have h := checkLog_sound (w := (629 / 1999371)) (n := 12)
    (lo := (629197 / 1000000000)) (hi := (314599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999371) = 1/(999371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13143 : Bounds (-314599 / 500000000) (-629197 / 1000000000) (Real.log (999371 / 1000000)) := by
  have h := reflection_log_13143_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13144_neg : (291118411 / 1000000000) ≤ -Real.log (1000000 / 1337923) ∧
    -Real.log (1000000 / 1337923) ≤ (72779603 / 250000000) := by
  have h := checkLog_sound (w := (337923 / 2337923)) (n := 12)
    (lo := (291118411 / 1000000000)) (hi := (72779603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337923 / 1000000) = 1/(1000000 / 1337923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13144 : Bounds (291118411 / 1000000000) (72779603 / 250000000) (Real.log (1337923 / 1000000)) := by
  have h := reflection_log_13144_neg
  have he : Real.log (1337923 / 1000000) = -Real.log (1000000 / 1337923) := by
    rw [show ((1337923 / 1000000) : ℝ) = ((1000000 / 1337923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13145_neg : (82474683 / 200000000) ≤ -Real.log (662077 / 1000000) ∧
    -Real.log (662077 / 1000000) ≤ (51546677 / 125000000) := by
  have h := checkLog_sound (w := (337923 / 1662077)) (n := 12)
    (lo := (82474683 / 200000000)) (hi := (51546677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 662077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 662077) = 1/(662077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13145 : Bounds (-51546677 / 125000000) (-82474683 / 200000000) (Real.log (662077 / 1000000)) := by
  have h := reflection_log_13145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13146_neg : (73241273 / 250000000) ≤ -Real.log (250000 / 335099) ∧
    -Real.log (250000 / 335099) ≤ (292965093 / 1000000000) := by
  have h := checkLog_sound (w := (85099 / 585099)) (n := 12)
    (lo := (73241273 / 250000000)) (hi := (292965093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335099 / 250000) = 1/(250000 / 335099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13146 : Bounds (73241273 / 250000000) (292965093 / 1000000000) (Real.log (335099 / 250000)) := by
  have h := reflection_log_13146_neg
  have he : Real.log (335099 / 250000) = -Real.log (250000 / 335099) := by
    rw [show ((335099 / 250000) : ℝ) = ((250000 / 335099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13147_neg : (52014453 / 125000000) ≤ -Real.log (164901 / 250000) ∧
    -Real.log (164901 / 250000) ≤ (133157 / 320000) := by
  have h := checkLog_sound (w := (85099 / 414901)) (n := 12)
    (lo := (52014453 / 125000000)) (hi := (133157 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164901) = 1/(164901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13147 : Bounds (-133157 / 320000) (-52014453 / 125000000) (Real.log (164901 / 250000)) := by
  have h := reflection_log_13147_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13148_neg : (123150531 / 1000000000) ≤ -Real.log (55258160199 / 62500000000) ∧
    -Real.log (55258160199 / 62500000000) ≤ (30787633 / 250000000) := by
  have h := checkLog_sound (w := (7241839801 / 117758160199)) (n := 12)
    (lo := (123150531 / 1000000000)) (hi := (30787633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55258160199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55258160199) = 1/(55258160199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13148 : Bounds (-30787633 / 250000000) (-123150531 / 1000000000) (Real.log (55258160199 / 62500000000)) := by
  have h := reflection_log_13148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13149_neg : (30313751 / 250000000) ≤ -Real.log (885808046071 / 1000000000000) ∧
    -Real.log (885808046071 / 1000000000000) ≤ (24251001 / 200000000) := by
  have h := checkLog_sound (w := (114191953929 / 1885808046071)) (n := 12)
    (lo := (30313751 / 250000000)) (hi := (24251001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 885808046071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 885808046071) = 1/(885808046071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13149 : Bounds (-24251001 / 200000000) (-30313751 / 250000000) (Real.log (885808046071 / 1000000000000)) := by
  have h := reflection_log_13149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13150_neg : (351745913 / 500000000) ≤ -Real.log (500000000000 / 1010398337353) ∧
    -Real.log (500000000000 / 1010398337353) ≤ (175872957 / 250000000) := by
  have h := checkLog_sound (w := (10398337353 / 2010398337353)) (n := 12)
    (lo := (5172323 / 500000000)) (hi := (10344647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1010398337353 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1010398337353 / 1000000000000) = 1/(500000000000 / 1010398337353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13150 : Bounds (351745913 / 500000000) (175872957 / 250000000) (Real.log (1010398337353 / 500000000000)) := by
  have h := reflection_log_13150_neg
  have he : Real.log (1010398337353 / 500000000000) = -Real.log (500000000000 / 1010398337353) := by
    rw [show ((1010398337353 / 500000000000) : ℝ) = ((500000000000 / 1010398337353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13151_neg : (177270179 / 250000000) ≤ -Real.log (500000000000 / 1016061151843) ∧
    -Real.log (500000000000 / 1016061151843) ≤ (354540359 / 500000000) := by
  have h := checkLog_sound (w := (16061151843 / 2016061151843)) (n := 12)
    (lo := (497923 / 31250000)) (hi := (15933537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1016061151843 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1016061151843 / 1000000000000) = 1/(500000000000 / 1016061151843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13151 : Bounds (177270179 / 250000000) (354540359 / 500000000) (Real.log (1016061151843 / 500000000000)) := by
  have h := reflection_log_13151_neg
  have he : Real.log (1016061151843 / 500000000000) = -Real.log (500000000000 / 1016061151843) := by
    rw [show ((1016061151843 / 500000000000) : ℝ) = ((500000000000 / 1016061151843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13152_neg : (1469622491 / 1000000000) ≤ -Real.log (500000000000 / 2173796791443) ∧
    -Real.log (500000000000 / 2173796791443) ≤ (734811247 / 500000000) := by
  have h := checkLog_sound (w := (173796791443 / 4173796791443)) (n := 12)
    (lo := (83328131 / 1000000000)) (hi := (20832033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2173796791443 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2173796791443 / 2000000000000) = 1/(500000000000 / 2173796791443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13152 : Bounds (1469622491 / 1000000000) (734811247 / 500000000) (Real.log (2173796791443 / 500000000000)) := by
  have h := reflection_log_13152_neg
  have he : Real.log (2173796791443 / 500000000000) = -Real.log (500000000000 / 2173796791443) := by
    rw [show ((2173796791443 / 500000000000) : ℝ) = ((500000000000 / 2173796791443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13153_neg : (184939943 / 125000000) ≤ -Real.log (250000000000 / 1097708894879) ∧
    -Real.log (250000000000 / 1097708894879) ≤ (1479519547 / 1000000000) := by
  have h := checkLog_sound (w := (97708894879 / 2097708894879)) (n := 12)
    (lo := (2913287 / 31250000)) (hi := (18645037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097708894879 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1097708894879 / 1000000000000) = 1/(250000000000 / 1097708894879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13153 : Bounds (184939943 / 125000000) (1479519547 / 1000000000) (Real.log (1097708894879 / 250000000000)) := by
  have h := reflection_log_13153_neg
  have he : Real.log (1097708894879 / 250000000000) = -Real.log (250000000000 / 1097708894879) := by
    rw [show ((1097708894879 / 250000000000) : ℝ) = ((250000000000 / 1097708894879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13154_neg : (30612891 / 62500000) ≤ -Real.log (125 / 204) ∧
    -Real.log (125 / 204) ≤ (489806257 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 329)) (n := 12)
    (lo := (30612891 / 62500000)) (hi := (489806257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204 / 125) = 1/(125 / 204) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13154 : Bounds (30612891 / 62500000) (489806257 / 1000000000) (Real.log (204 / 125)) := by
  have h := reflection_log_13154_neg
  have he : Real.log (204 / 125) = -Real.log (125 / 204) := by
    rw [show ((204 / 125) : ℝ) = ((125 / 204) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13155_neg : (49983617 / 50000000) ≤ -Real.log (46 / 125) ∧
    -Real.log (46 / 125) ≤ (499836171 / 500000000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 92) = 1/(46 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13155 : Bounds (-499836171 / 500000000) (-49983617 / 50000000) (Real.log (46 / 125)) := by
  have h := reflection_log_13155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13156_neg : (3159 / 5000000) ≤ -Real.log (125000 / 125079) ∧
    -Real.log (125000 / 125079) ≤ (631801 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 250079)) (n := 12)
    (lo := (3159 / 5000000)) (hi := (631801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125079 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125079 / 125000) = 1/(125000 / 125079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13156 : Bounds (3159 / 5000000) (631801 / 1000000000) (Real.log (125079 / 125000)) := by
  have h := reflection_log_13156_neg
  have he : Real.log (125079 / 125000) = -Real.log (125000 / 125079) := by
    rw [show ((125079 / 125000) : ℝ) = ((125000 / 125079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13157_neg : (632199 / 1000000000) ≤ -Real.log (124921 / 125000) ∧
    -Real.log (124921 / 125000) ≤ (3161 / 5000000) := by
  have h := checkLog_sound (w := (79 / 249921)) (n := 12)
    (lo := (632199 / 1000000000)) (hi := (3161 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124921) = 1/(124921 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13157 : Bounds (-3161 / 5000000) (-632199 / 1000000000) (Real.log (124921 / 125000)) := by
  have h := reflection_log_13157_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13158_neg : (146269131 / 500000000) ≤ -Real.log (62500 / 83739) ∧
    -Real.log (62500 / 83739) ≤ (292538263 / 1000000000) := by
  have h := checkLog_sound (w := (21239 / 146239)) (n := 12)
    (lo := (146269131 / 500000000)) (hi := (292538263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83739 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83739 / 62500) = 1/(62500 / 83739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13158 : Bounds (146269131 / 500000000) (292538263 / 1000000000) (Real.log (83739 / 62500)) := by
  have h := reflection_log_13158_neg
  have he : Real.log (83739 / 62500) = -Real.log (62500 / 83739) := by
    rw [show ((83739 / 62500) : ℝ) = ((62500 / 83739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13159_neg : (103812203 / 250000000) ≤ -Real.log (41261 / 62500) ∧
    -Real.log (41261 / 62500) ≤ (415248813 / 1000000000) := by
  have h := checkLog_sound (w := (21239 / 103761)) (n := 12)
    (lo := (103812203 / 250000000)) (hi := (415248813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 41261) = 1/(41261 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13159 : Bounds (-415248813 / 1000000000) (-103812203 / 250000000) (Real.log (41261 / 62500)) := by
  have h := reflection_log_13159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13160_neg : (14719377 / 50000000) ≤ -Real.log (31250 / 41947) ∧
    -Real.log (31250 / 41947) ≤ (294387541 / 1000000000) := by
  have h := checkLog_sound (w := (10697 / 73197)) (n := 12)
    (lo := (14719377 / 50000000)) (hi := (294387541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41947 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41947 / 31250) = 1/(31250 / 41947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13160 : Bounds (14719377 / 50000000) (294387541 / 1000000000) (Real.log (41947 / 31250)) := by
  have h := reflection_log_13160_neg
  have he : Real.log (41947 / 31250) = -Real.log (31250 / 41947) := by
    rw [show ((41947 / 31250) : ℝ) = ((31250 / 41947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13161_neg : (20950623 / 50000000) ≤ -Real.log (20553 / 31250) ∧
    -Real.log (20553 / 31250) ≤ (419012461 / 1000000000) := by
  have h := checkLog_sound (w := (10697 / 51803)) (n := 12)
    (lo := (20950623 / 50000000)) (hi := (419012461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20553) = 1/(20553 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13161 : Bounds (-419012461 / 1000000000) (-20950623 / 50000000) (Real.log (20553 / 31250)) := by
  have h := reflection_log_13161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13162_neg : (3115623 / 25000000) ≤ -Real.log (862136691 / 976562500) ∧
    -Real.log (862136691 / 976562500) ≤ (124624921 / 1000000000) := by
  have h := checkLog_sound (w := (114425809 / 1838699191)) (n := 12)
    (lo := (3115623 / 25000000)) (hi := (124624921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 862136691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 862136691) = 1/(862136691 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13162 : Bounds (-124624921 / 1000000000) (-3115623 / 25000000) (Real.log (862136691 / 976562500)) := by
  have h := reflection_log_13162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13163_neg : (2454211 / 20000000) ≤ -Real.log (3455154879 / 3906250000) ∧
    -Real.log (3455154879 / 3906250000) ≤ (122710551 / 1000000000) := by
  have h := checkLog_sound (w := (451095121 / 7361404879)) (n := 12)
    (lo := (2454211 / 20000000)) (hi := (122710551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3455154879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3455154879) = 1/(3455154879 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13163 : Bounds (-122710551 / 1000000000) (-2454211 / 20000000) (Real.log (3455154879 / 3906250000)) := by
  have h := reflection_log_13163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13164_neg : (353893537 / 500000000) ≤ -Real.log (250000000000 / 507373791231) ∧
    -Real.log (250000000000 / 507373791231) ≤ (176946769 / 250000000) := by
  have h := checkLog_sound (w := (7373791231 / 1007373791231)) (n := 12)
    (lo := (7319947 / 500000000)) (hi := (2927979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507373791231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(507373791231 / 500000000000) = 1/(250000000000 / 507373791231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13164 : Bounds (353893537 / 500000000) (176946769 / 250000000) (Real.log (507373791231 / 250000000000)) := by
  have h := reflection_log_13164_neg
  have he : Real.log (507373791231 / 250000000000) = -Real.log (250000000000 / 507373791231) := by
    rw [show ((507373791231 / 250000000000) : ℝ) = ((250000000000 / 507373791231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13165_neg : (3567 / 5000) ≤ -Real.log (250000000000 / 510229650173) ∧
    -Real.log (250000000000 / 510229650173) ≤ (356700001 / 500000000) := by
  have h := checkLog_sound (w := (10229650173 / 1010229650173)) (n := 12)
    (lo := (1012641 / 50000000)) (hi := (20252821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((510229650173 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(510229650173 / 500000000000) = 1/(250000000000 / 510229650173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13165 : Bounds (3567 / 5000) (356700001 / 500000000) (Real.log (510229650173 / 250000000000)) := by
  have h := reflection_log_13165_neg
  have he : Real.log (510229650173 / 250000000000) = -Real.log (250000000000 / 510229650173) := by
    rw [show ((510229650173 / 250000000000) : ℝ) = ((250000000000 / 510229650173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13166_neg : (184939943 / 125000000) ≤ -Real.log (500000000000 / 2195417789757) ∧
    -Real.log (500000000000 / 2195417789757) ≤ (1479519547 / 1000000000) := by
  have h := checkLog_sound (w := (195417789757 / 4195417789757)) (n := 12)
    (lo := (2913287 / 31250000)) (hi := (18645037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2195417789757 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2195417789757 / 2000000000000) = 1/(500000000000 / 2195417789757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13166 : Bounds (184939943 / 125000000) (1479519547 / 1000000000) (Real.log (2195417789757 / 500000000000)) := by
  have h := reflection_log_13166_neg
  have he : Real.log (2195417789757 / 500000000000) = -Real.log (500000000000 / 2195417789757) := by
    rw [show ((2195417789757 / 500000000000) : ℝ) = ((500000000000 / 2195417789757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13167_neg : (372369649 / 250000000) ≤ -Real.log (125000000000 / 554347826087) ∧
    -Real.log (125000000000 / 554347826087) ≤ (1489478599 / 1000000000) := by
  have h := checkLog_sound (w := (54347826087 / 1054347826087)) (n := 12)
    (lo := (25796059 / 250000000)) (hi := (103184237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554347826087 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(554347826087 / 500000000000) = 1/(125000000000 / 554347826087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13167 : Bounds (372369649 / 250000000) (1489478599 / 1000000000) (Real.log (554347826087 / 125000000000)) := by
  have h := reflection_log_13167_neg
  have he : Real.log (554347826087 / 125000000000) = -Real.log (125000000000 / 554347826087) := by
    rw [show ((554347826087 / 125000000000) : ℝ) = ((125000000000 / 554347826087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13168_neg : (122910701 / 250000000) ≤ -Real.log (200 / 327) ∧
    -Real.log (200 / 327) ≤ (98328561 / 200000000) := by
  have h := checkLog_sound (w := (127 / 527)) (n := 12)
    (lo := (122910701 / 250000000)) (hi := (98328561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 200) = 1/(200 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13168 : Bounds (122910701 / 250000000) (98328561 / 200000000) (Real.log (327 / 200)) := by
  have h := reflection_log_13168_neg
  have he : Real.log (327 / 200) = -Real.log (200 / 327) := by
    rw [show ((327 / 200) : ℝ) = ((200 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13169_neg : (251964481 / 250000000) ≤ -Real.log (73 / 200) ∧
    -Real.log (73 / 200) ≤ (503928963 / 500000000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 73) = 1/(73 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13169 : Bounds (-503928963 / 500000000) (-251964481 / 250000000) (Real.log (73 / 200)) := by
  have h := reflection_log_13169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13170_neg : (317399 / 500000000) ≤ -Real.log (200000 / 200127) ∧
    -Real.log (200000 / 200127) ≤ (634799 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 400127)) (n := 12)
    (lo := (317399 / 500000000)) (hi := (634799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200127 / 200000) = 1/(200000 / 200127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13170 : Bounds (317399 / 500000000) (634799 / 1000000000) (Real.log (200127 / 200000)) := by
  have h := reflection_log_13170_neg
  have he : Real.log (200127 / 200000) = -Real.log (200000 / 200127) := by
    rw [show ((200127 / 200000) : ℝ) = ((200000 / 200127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13171_neg : (635201 / 1000000000) ≤ -Real.log (199873 / 200000) ∧
    -Real.log (199873 / 200000) ≤ (317601 / 500000000) := by
  have h := checkLog_sound (w := (127 / 399873)) (n := 12)
    (lo := (635201 / 1000000000)) (hi := (317601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199873) = 1/(199873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13171 : Bounds (-317601 / 500000000) (-635201 / 1000000000) (Real.log (199873 / 200000)) := by
  have h := reflection_log_13171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13172_neg : (7348977 / 25000000) ≤ -Real.log (1000000 / 1341729) ∧
    -Real.log (1000000 / 1341729) ≤ (293959081 / 1000000000) := by
  have h := checkLog_sound (w := (341729 / 2341729)) (n := 12)
    (lo := (7348977 / 25000000)) (hi := (293959081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341729 / 1000000) = 1/(1000000 / 1341729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13172 : Bounds (7348977 / 25000000) (293959081 / 1000000000) (Real.log (1341729 / 1000000)) := by
  have h := reflection_log_13172_neg
  have he : Real.log (1341729 / 1000000) = -Real.log (1000000 / 1341729) := by
    rw [show ((1341729 / 1000000) : ℝ) = ((1000000 / 1341729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13173_neg : (209069289 / 500000000) ≤ -Real.log (658271 / 1000000) ∧
    -Real.log (658271 / 1000000) ≤ (418138579 / 1000000000) := by
  have h := checkLog_sound (w := (341729 / 1658271)) (n := 12)
    (lo := (209069289 / 500000000)) (hi := (418138579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658271) = 1/(658271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13173 : Bounds (-418138579 / 1000000000) (-209069289 / 500000000) (Real.log (658271 / 1000000)) := by
  have h := reflection_log_13173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13174_neg : (295810943 / 1000000000) ≤ -Real.log (125000 / 168027) ∧
    -Real.log (125000 / 168027) ≤ (2311023 / 7812500) := by
  have h := checkLog_sound (w := (43027 / 293027)) (n := 12)
    (lo := (295810943 / 1000000000)) (hi := (2311023 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168027 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168027 / 125000) = 1/(125000 / 168027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13174 : Bounds (295810943 / 1000000000) (2311023 / 7812500) (Real.log (168027 / 125000)) := by
  have h := reflection_log_13174_neg
  have he : Real.log (168027 / 125000) = -Real.log (125000 / 168027) := by
    rw [show ((168027 / 125000) : ℝ) = ((125000 / 168027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13175_neg : (105480953 / 250000000) ≤ -Real.log (81973 / 125000) ∧
    -Real.log (81973 / 125000) ≤ (421923813 / 1000000000) := by
  have h := checkLog_sound (w := (43027 / 206973)) (n := 12)
    (lo := (105480953 / 250000000)) (hi := (421923813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 81973) = 1/(81973 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13175 : Bounds (-421923813 / 1000000000) (-105480953 / 250000000) (Real.log (81973 / 125000)) := by
  have h := reflection_log_13175_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13176_neg : (126112869 / 1000000000) ≤ -Real.log (13773677271 / 15625000000) ∧
    -Real.log (13773677271 / 15625000000) ≤ (12611287 / 100000000) := by
  have h := checkLog_sound (w := (1851322729 / 29398677271)) (n := 12)
    (lo := (126112869 / 1000000000)) (hi := (12611287 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 13773677271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 13773677271) = 1/(13773677271 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13176 : Bounds (-12611287 / 100000000) (-126112869 / 1000000000) (Real.log (13773677271 / 15625000000)) := by
  have h := reflection_log_13176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13177_neg : (124179497 / 1000000000) ≤ -Real.log (883221290559 / 1000000000000) ∧
    -Real.log (883221290559 / 1000000000000) ≤ (62089749 / 500000000) := by
  have h := checkLog_sound (w := (116778709441 / 1883221290559)) (n := 12)
    (lo := (124179497 / 1000000000)) (hi := (62089749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 883221290559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 883221290559) = 1/(883221290559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13177 : Bounds (-62089749 / 500000000) (-124179497 / 1000000000) (Real.log (883221290559 / 1000000000000)) := by
  have h := reflection_log_13177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13178_neg : (356048829 / 500000000) ≤ -Real.log (976562500 / 1990490583) ∧
    -Real.log (976562500 / 1990490583) ≤ (35604883 / 50000000) := by
  have h := checkLog_sound (w := (37365583 / 3943615583)) (n := 12)
    (lo := (9475239 / 500000000)) (hi := (18950479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1990490583 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1990490583 / 1953125000) = 1/(976562500 / 1990490583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13178 : Bounds (356048829 / 500000000) (35604883 / 50000000) (Real.log (1990490583 / 976562500)) := by
  have h := reflection_log_13178_neg
  have he : Real.log (1990490583 / 976562500) = -Real.log (976562500 / 1990490583) := by
    rw [show ((1990490583 / 976562500) : ℝ) = ((976562500 / 1990490583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13179_neg : (143546951 / 200000000) ≤ -Real.log (500000000000 / 1024892342601) ∧
    -Real.log (500000000000 / 1024892342601) ≤ (717734757 / 1000000000) := by
  have h := checkLog_sound (w := (24892342601 / 2024892342601)) (n := 12)
    (lo := (983503 / 40000000)) (hi := (3073447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024892342601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1024892342601 / 1000000000000) = 1/(500000000000 / 1024892342601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13179 : Bounds (143546951 / 200000000) (717734757 / 1000000000) (Real.log (1024892342601 / 500000000000)) := by
  have h := reflection_log_13179_neg
  have he : Real.log (1024892342601 / 500000000000) = -Real.log (500000000000 / 1024892342601) := by
    rw [show ((1024892342601 / 500000000000) : ℝ) = ((500000000000 / 1024892342601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13180_neg : (372369649 / 250000000) ≤ -Real.log (500000000000 / 2217391304347) ∧
    -Real.log (500000000000 / 2217391304347) ≤ (1489478599 / 1000000000) := by
  have h := checkLog_sound (w := (217391304347 / 4217391304347)) (n := 12)
    (lo := (25796059 / 250000000)) (hi := (103184237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2217391304347 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2217391304347 / 2000000000000) = 1/(500000000000 / 2217391304347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13180 : Bounds (372369649 / 250000000) (1489478599 / 1000000000) (Real.log (2217391304347 / 500000000000)) := by
  have h := reflection_log_13180_neg
  have he : Real.log (2217391304347 / 500000000000) = -Real.log (500000000000 / 2217391304347) := by
    rw [show ((2217391304347 / 500000000000) : ℝ) = ((500000000000 / 2217391304347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13181_neg : (187437591 / 125000000) ≤ -Real.log (250000000000 / 1119863013699) ∧
    -Real.log (250000000000 / 1119863013699) ≤ (1499500731 / 1000000000) := by
  have h := checkLog_sound (w := (119863013699 / 2119863013699)) (n := 12)
    (lo := (3537699 / 31250000)) (hi := (113206369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119863013699 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1119863013699 / 1000000000000) = 1/(250000000000 / 1119863013699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13181 : Bounds (187437591 / 125000000) (1499500731 / 1000000000) (Real.log (1119863013699 / 250000000000)) := by
  have h := reflection_log_13181_neg
  have he : Real.log (1119863013699 / 250000000000) = -Real.log (250000000000 / 1119863013699) := by
    rw [show ((1119863013699 / 250000000000) : ℝ) = ((250000000000 / 1119863013699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13182_neg : (98695197 / 200000000) ≤ -Real.log (500 / 819) ∧
    -Real.log (500 / 819) ≤ (246737993 / 500000000) := by
  have h := checkLog_sound (w := (319 / 1319)) (n := 12)
    (lo := (98695197 / 200000000)) (hi := (246737993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819 / 500) = 1/(500 / 819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13182 : Bounds (98695197 / 200000000) (246737993 / 500000000) (Real.log (819 / 500)) := by
  have h := reflection_log_13182_neg
  have he : Real.log (819 / 500) = -Real.log (500 / 819) := by
    rw [show ((819 / 500) : ℝ) = ((500 / 819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13183_neg : (508055533 / 500000000) ≤ -Real.log (181 / 500) ∧
    -Real.log (181 / 500) ≤ (254027767 / 250000000) := by
  have h := checkLog_sound (w := (69 / 431)) (n := 12)
    (lo := (161481943 / 500000000)) (hi := (322963887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 181) = 1/(181 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13183 : Bounds (-254027767 / 250000000) (-508055533 / 500000000) (Real.log (181 / 500)) := by
  have h := reflection_log_13183_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0206 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13184_neg : (159449 / 250000000) ≤ -Real.log (500000 / 500319) ∧
    -Real.log (500000 / 500319) ≤ (637797 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1000319)) (n := 12)
    (lo := (159449 / 250000000)) (hi := (637797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500319 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500319 / 500000) = 1/(500000 / 500319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13184 : Bounds (159449 / 250000000) (637797 / 1000000000) (Real.log (500319 / 500000)) := by
  have h := reflection_log_13184_neg
  have he : Real.log (500319 / 500000) = -Real.log (500000 / 500319) := by
    rw [show ((500319 / 500000) : ℝ) = ((500000 / 500319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13185_neg : (638203 / 1000000000) ≤ -Real.log (499681 / 500000) ∧
    -Real.log (499681 / 500000) ≤ (159551 / 250000000) := by
  have h := checkLog_sound (w := (319 / 999681)) (n := 12)
    (lo := (638203 / 1000000000)) (hi := (159551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499681) = 1/(499681 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13185 : Bounds (-159551 / 250000000) (-638203 / 1000000000) (Real.log (499681 / 500000)) := by
  have h := reflection_log_13185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13186_neg : (295382349 / 1000000000) ≤ -Real.log (25000 / 33591) ∧
    -Real.log (25000 / 33591) ≤ (5907647 / 20000000) := by
  have h := checkLog_sound (w := (8591 / 58591)) (n := 12)
    (lo := (295382349 / 1000000000)) (hi := (5907647 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33591 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33591 / 25000) = 1/(25000 / 33591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13186 : Bounds (295382349 / 1000000000) (5907647 / 20000000) (Real.log (33591 / 25000)) := by
  have h := reflection_log_13186_neg
  have he : Real.log (33591 / 25000) = -Real.log (25000 / 33591) := by
    rw [show ((33591 / 25000) : ℝ) = ((25000 / 33591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13187_neg : (21052293 / 50000000) ≤ -Real.log (16409 / 25000) ∧
    -Real.log (16409 / 25000) ≤ (421045861 / 1000000000) := by
  have h := checkLog_sound (w := (8591 / 41409)) (n := 12)
    (lo := (21052293 / 50000000)) (hi := (421045861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 16409) = 1/(16409 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13187 : Bounds (-421045861 / 1000000000) (-21052293 / 50000000) (Real.log (16409 / 25000)) := by
  have h := reflection_log_13187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13188_neg : (14861839 / 50000000) ≤ -Real.log (500000 / 673067) ∧
    -Real.log (500000 / 673067) ≤ (297236781 / 1000000000) := by
  have h := checkLog_sound (w := (173067 / 1173067)) (n := 12)
    (lo := (14861839 / 50000000)) (hi := (297236781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673067 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673067 / 500000) = 1/(500000 / 673067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13188 : Bounds (14861839 / 50000000) (297236781 / 1000000000) (Real.log (673067 / 500000)) := by
  have h := reflection_log_13188_neg
  have he : Real.log (673067 / 500000) = -Real.log (500000 / 673067) := by
    rw [show ((673067 / 500000) : ℝ) = ((500000 / 673067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13189_neg : (424852841 / 1000000000) ≤ -Real.log (326933 / 500000) ∧
    -Real.log (326933 / 500000) ≤ (212426421 / 500000000) := by
  have h := checkLog_sound (w := (173067 / 826933)) (n := 12)
    (lo := (424852841 / 1000000000)) (hi := (212426421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326933) = 1/(326933 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13189 : Bounds (-212426421 / 500000000) (-424852841 / 1000000000) (Real.log (326933 / 500000)) := by
  have h := reflection_log_13189_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13190_neg : (6380803 / 50000000) ≤ -Real.log (220047813511 / 250000000000) ∧
    -Real.log (220047813511 / 250000000000) ≤ (127616061 / 1000000000) := by
  have h := checkLog_sound (w := (29952186489 / 470047813511)) (n := 12)
    (lo := (6380803 / 50000000)) (hi := (127616061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 220047813511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 220047813511) = 1/(220047813511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13190 : Bounds (-127616061 / 1000000000) (-6380803 / 50000000) (Real.log (220047813511 / 250000000000)) := by
  have h := reflection_log_13190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13191_neg : (12566351 / 100000000) ≤ -Real.log (551194719 / 625000000) ∧
    -Real.log (551194719 / 625000000) ≤ (125663511 / 1000000000) := by
  have h := checkLog_sound (w := (73805281 / 1176194719)) (n := 12)
    (lo := (12566351 / 100000000)) (hi := (125663511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 551194719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 551194719) = 1/(551194719 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13191 : Bounds (-125663511 / 1000000000) (-12566351 / 100000000) (Real.log (551194719 / 625000000)) := by
  have h := reflection_log_13191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13192_neg : (44776763 / 62500000) ≤ -Real.log (250000000000 / 511777073557) ∧
    -Real.log (250000000000 / 511777073557) ≤ (71642821 / 100000000) := by
  have h := checkLog_sound (w := (11777073557 / 1011777073557)) (n := 12)
    (lo := (5820257 / 250000000)) (hi := (23281029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511777073557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(511777073557 / 500000000000) = 1/(250000000000 / 511777073557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13192 : Bounds (44776763 / 62500000) (71642821 / 100000000) (Real.log (511777073557 / 250000000000)) := by
  have h := reflection_log_13192_neg
  have he : Real.log (511777073557 / 250000000000) = -Real.log (250000000000 / 511777073557) := by
    rw [show ((511777073557 / 250000000000) : ℝ) = ((250000000000 / 511777073557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13193_neg : (722089621 / 1000000000) ≤ -Real.log (50000000000 / 102936534397) ∧
    -Real.log (50000000000 / 102936534397) ≤ (722089623 / 1000000000) := by
  have h := checkLog_sound (w := (2936534397 / 202936534397)) (n := 12)
    (lo := (28942441 / 1000000000)) (hi := (14471221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102936534397 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102936534397 / 100000000000) = 1/(50000000000 / 102936534397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13193 : Bounds (722089621 / 1000000000) (722089623 / 1000000000) (Real.log (102936534397 / 50000000000)) := by
  have h := reflection_log_13193_neg
  have he : Real.log (102936534397 / 50000000000) = -Real.log (50000000000 / 102936534397) := by
    rw [show ((102936534397 / 50000000000) : ℝ) = ((50000000000 / 102936534397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13194_neg : (187437591 / 125000000) ≤ -Real.log (500000000000 / 2239726027397) ∧
    -Real.log (500000000000 / 2239726027397) ≤ (1499500731 / 1000000000) := by
  have h := checkLog_sound (w := (239726027397 / 4239726027397)) (n := 12)
    (lo := (3537699 / 31250000)) (hi := (113206369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2239726027397 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2239726027397 / 2000000000000) = 1/(500000000000 / 2239726027397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13194 : Bounds (187437591 / 125000000) (1499500731 / 1000000000) (Real.log (2239726027397 / 500000000000)) := by
  have h := reflection_log_13194_neg
  have he : Real.log (2239726027397 / 500000000000) = -Real.log (500000000000 / 2239726027397) := by
    rw [show ((2239726027397 / 500000000000) : ℝ) = ((500000000000 / 2239726027397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13195_neg : (1509587051 / 1000000000) ≤ -Real.log (500000000000 / 2262430939227) ∧
    -Real.log (500000000000 / 2262430939227) ≤ (754793527 / 500000000) := by
  have h := checkLog_sound (w := (262430939227 / 4262430939227)) (n := 12)
    (lo := (123292691 / 1000000000)) (hi := (30823173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2262430939227 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2262430939227 / 2000000000000) = 1/(500000000000 / 2262430939227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13195 : Bounds (1509587051 / 1000000000) (754793527 / 500000000) (Real.log (2262430939227 / 500000000000)) := by
  have h := reflection_log_13195_neg
  have he : Real.log (2262430939227 / 500000000000) = -Real.log (500000000000 / 2262430939227) := by
    rw [show ((2262430939227 / 500000000000) : ℝ) = ((500000000000 / 2262430939227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13196_neg : (123826453 / 250000000) ≤ -Real.log (1000 / 1641) ∧
    -Real.log (1000 / 1641) ≤ (495305813 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 2641)) (n := 12)
    (lo := (123826453 / 250000000)) (hi := (495305813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641 / 1000) = 1/(1000 / 1641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13196 : Bounds (123826453 / 250000000) (495305813 / 1000000000) (Real.log (1641 / 1000)) := by
  have h := reflection_log_13196_neg
  have he : Real.log (1641 / 1000) = -Real.log (1000 / 1641) := by
    rw [show ((1641 / 1000) : ℝ) = ((1000 / 1641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13197_neg : (1024432889 / 1000000000) ≤ -Real.log (359 / 1000) ∧
    -Real.log (359 / 1000) ≤ (1024432891 / 1000000000) := by
  have h := checkLog_sound (w := (141 / 859)) (n := 12)
    (lo := (331285709 / 1000000000)) (hi := (33128571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 359) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 359) = 1/(359 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13197 : Bounds (-1024432891 / 1000000000) (-1024432889 / 1000000000) (Real.log (359 / 1000)) := by
  have h := reflection_log_13197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13198_neg : (320397 / 500000000) ≤ -Real.log (1000000 / 1000641) ∧
    -Real.log (1000000 / 1000641) ≤ (128159 / 200000000) := by
  have h := checkLog_sound (w := (641 / 2000641)) (n := 12)
    (lo := (320397 / 500000000)) (hi := (128159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000641 / 1000000) = 1/(1000000 / 1000641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13198 : Bounds (320397 / 500000000) (128159 / 200000000) (Real.log (1000641 / 1000000)) := by
  have h := reflection_log_13198_neg
  have he : Real.log (1000641 / 1000000) = -Real.log (1000000 / 1000641) := by
    rw [show ((1000641 / 1000000) : ℝ) = ((1000000 / 1000641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13199_neg : (128241 / 200000000) ≤ -Real.log (999359 / 1000000) ∧
    -Real.log (999359 / 1000000) ≤ (320603 / 500000000) := by
  have h := checkLog_sound (w := (641 / 1999359)) (n := 12)
    (lo := (128241 / 200000000)) (hi := (320603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999359) = 1/(999359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13199 : Bounds (-320603 / 500000000) (-128241 / 200000000) (Real.log (999359 / 1000000)) := by
  have h := reflection_log_13199_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13200_neg : (296806567 / 1000000000) ≤ -Real.log (200000 / 269111) ∧
    -Real.log (200000 / 269111) ≤ (37100821 / 125000000) := by
  have h := checkLog_sound (w := (69111 / 469111)) (n := 12)
    (lo := (296806567 / 1000000000)) (hi := (37100821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269111 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269111 / 200000) = 1/(200000 / 269111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13200 : Bounds (296806567 / 1000000000) (37100821 / 125000000) (Real.log (269111 / 200000)) := by
  have h := reflection_log_13200_neg
  have he : Real.log (269111 / 200000) = -Real.log (200000 / 269111) := by
    rw [show ((269111 / 200000) : ℝ) = ((200000 / 269111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13201_neg : (42396773 / 100000000) ≤ -Real.log (130889 / 200000) ∧
    -Real.log (130889 / 200000) ≤ (423967731 / 1000000000) := by
  have h := checkLog_sound (w := (69111 / 330889)) (n := 12)
    (lo := (42396773 / 100000000)) (hi := (423967731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 130889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 130889) = 1/(130889 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13201 : Bounds (-423967731 / 1000000000) (-42396773 / 100000000) (Real.log (130889 / 200000)) := by
  have h := reflection_log_13201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13202_neg : (37333037 / 125000000) ≤ -Real.log (1000000 / 1348057) ∧
    -Real.log (1000000 / 1348057) ≤ (298664297 / 1000000000) := by
  have h := checkLog_sound (w := (348057 / 2348057)) (n := 12)
    (lo := (37333037 / 125000000)) (hi := (298664297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348057 / 1000000) = 1/(1000000 / 1348057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13202 : Bounds (37333037 / 125000000) (298664297 / 1000000000) (Real.log (1348057 / 1000000)) := by
  have h := reflection_log_13202_neg
  have he : Real.log (1348057 / 1000000) = -Real.log (1000000 / 1348057) := by
    rw [show ((1348057 / 1000000) : ℝ) = ((1000000 / 1348057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13203_neg : (3342173 / 7812500) ≤ -Real.log (651943 / 1000000) ∧
    -Real.log (651943 / 1000000) ≤ (85559629 / 200000000) := by
  have h := checkLog_sound (w := (348057 / 1651943)) (n := 12)
    (lo := (3342173 / 7812500)) (hi := (85559629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651943) = 1/(651943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13203 : Bounds (-85559629 / 200000000) (-3342173 / 7812500) (Real.log (651943 / 1000000)) := by
  have h := reflection_log_13203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13204_neg : (129133847 / 1000000000) ≤ -Real.log (878856324751 / 1000000000000) ∧
    -Real.log (878856324751 / 1000000000000) ≤ (16141731 / 125000000) := by
  have h := checkLog_sound (w := (121143675249 / 1878856324751)) (n := 12)
    (lo := (129133847 / 1000000000)) (hi := (16141731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 878856324751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 878856324751) = 1/(878856324751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13204 : Bounds (-16141731 / 125000000) (-129133847 / 1000000000) (Real.log (878856324751 / 1000000000000)) := by
  have h := reflection_log_13204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13205_neg : (127161163 / 1000000000) ≤ -Real.log (35223669679 / 40000000000) ∧
    -Real.log (35223669679 / 40000000000) ≤ (31790291 / 250000000) := by
  have h := checkLog_sound (w := (4776330321 / 75223669679)) (n := 12)
    (lo := (127161163 / 1000000000)) (hi := (31790291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 35223669679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 35223669679) = 1/(35223669679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13205 : Bounds (-31790291 / 250000000) (-127161163 / 1000000000) (Real.log (35223669679 / 40000000000)) := by
  have h := reflection_log_13205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13206_neg : (720774297 / 1000000000) ≤ -Real.log (250000000000 / 514006142609) ∧
    -Real.log (250000000000 / 514006142609) ≤ (720774299 / 1000000000) := by
  have h := checkLog_sound (w := (14006142609 / 1014006142609)) (n := 12)
    (lo := (27627117 / 1000000000)) (hi := (13813559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514006142609 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(514006142609 / 500000000000) = 1/(250000000000 / 514006142609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13206 : Bounds (720774297 / 1000000000) (720774299 / 1000000000) (Real.log (514006142609 / 250000000000)) := by
  have h := reflection_log_13206_neg
  have he : Real.log (514006142609 / 250000000000) = -Real.log (250000000000 / 514006142609) := by
    rw [show ((514006142609 / 250000000000) : ℝ) = ((250000000000 / 514006142609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13207_neg : (18161561 / 25000000) ≤ -Real.log (62500000000 / 129234553481) ∧
    -Real.log (62500000000 / 129234553481) ≤ (363231221 / 500000000) := by
  have h := checkLog_sound (w := (4234553481 / 254234553481)) (n := 12)
    (lo := (1665763 / 50000000)) (hi := (33315261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129234553481 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(129234553481 / 125000000000) = 1/(62500000000 / 129234553481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13207 : Bounds (18161561 / 25000000) (363231221 / 500000000) (Real.log (129234553481 / 62500000000)) := by
  have h := reflection_log_13207_neg
  have he : Real.log (129234553481 / 62500000000) = -Real.log (62500000000 / 129234553481) := by
    rw [show ((129234553481 / 62500000000) : ℝ) = ((62500000000 / 129234553481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13208_neg : (1509587051 / 1000000000) ≤ -Real.log (250000000000 / 1131215469613) ∧
    -Real.log (250000000000 / 1131215469613) ≤ (754793527 / 500000000) := by
  have h := checkLog_sound (w := (131215469613 / 2131215469613)) (n := 12)
    (lo := (123292691 / 1000000000)) (hi := (30823173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131215469613 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1131215469613 / 1000000000000) = 1/(250000000000 / 1131215469613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13208 : Bounds (1509587051 / 1000000000) (754793527 / 500000000) (Real.log (1131215469613 / 250000000000)) := by
  have h := reflection_log_13208_neg
  have he : Real.log (1131215469613 / 250000000000) = -Real.log (250000000000 / 1131215469613) := by
    rw [show ((1131215469613 / 250000000000) : ℝ) = ((250000000000 / 1131215469613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13209_neg : (1519738701 / 1000000000) ≤ -Real.log (100000000000 / 457103064067) ∧
    -Real.log (100000000000 / 457103064067) ≤ (94983669 / 62500000) := by
  have h := checkLog_sound (w := (57103064067 / 857103064067)) (n := 12)
    (lo := (133444341 / 1000000000)) (hi := (66722171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457103064067 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(457103064067 / 400000000000) = 1/(100000000000 / 457103064067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13209 : Bounds (1519738701 / 1000000000) (94983669 / 62500000) (Real.log (457103064067 / 100000000000)) := by
  have h := reflection_log_13209_neg
  have he : Real.log (457103064067 / 100000000000) = -Real.log (100000000000 / 457103064067) := by
    rw [show ((457103064067 / 100000000000) : ℝ) = ((100000000000 / 457103064067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13210_neg : (62141537 / 125000000) ≤ -Real.log (250 / 411) ∧
    -Real.log (250 / 411) ≤ (497132297 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 661)) (n := 12)
    (lo := (62141537 / 125000000)) (hi := (497132297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411 / 250) = 1/(250 / 411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13210 : Bounds (62141537 / 125000000) (497132297 / 1000000000) (Real.log (411 / 250)) := by
  have h := reflection_log_13210_neg
  have he : Real.log (411 / 250) = -Real.log (250 / 411) := by
    rw [show ((411 / 250) : ℝ) = ((250 / 411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13211_neg : (1032824547 / 1000000000) ≤ -Real.log (89 / 250) ∧
    -Real.log (89 / 250) ≤ (1032824549 / 1000000000) := by
  have h := checkLog_sound (w := (18 / 107)) (n := 12)
    (lo := (339677367 / 1000000000)) (hi := (42459671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 89) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 89) = 1/(89 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13211 : Bounds (-1032824549 / 1000000000) (-1032824547 / 1000000000) (Real.log (89 / 250)) := by
  have h := reflection_log_13211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13212_neg : (40237 / 62500000) ≤ -Real.log (250000 / 250161) ∧
    -Real.log (250000 / 250161) ≤ (643793 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 500161)) (n := 12)
    (lo := (40237 / 62500000)) (hi := (643793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250161 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250161 / 250000) = 1/(250000 / 250161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13212 : Bounds (40237 / 62500000) (643793 / 1000000000) (Real.log (250161 / 250000)) := by
  have h := reflection_log_13212_neg
  have he : Real.log (250161 / 250000) = -Real.log (250000 / 250161) := by
    rw [show ((250161 / 250000) : ℝ) = ((250000 / 250161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13213_neg : (644207 / 1000000000) ≤ -Real.log (249839 / 250000) ∧
    -Real.log (249839 / 250000) ≤ (40263 / 62500000) := by
  have h := checkLog_sound (w := (161 / 499839)) (n := 12)
    (lo := (644207 / 1000000000)) (hi := (40263 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249839) = 1/(249839 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13213 : Bounds (-40263 / 62500000) (-644207 / 1000000000) (Real.log (249839 / 250000)) := by
  have h := reflection_log_13213_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13214_neg : (74558303 / 250000000) ≤ -Real.log (250000 / 336869) ∧
    -Real.log (250000 / 336869) ≤ (298233213 / 1000000000) := by
  have h := checkLog_sound (w := (86869 / 586869)) (n := 12)
    (lo := (74558303 / 250000000)) (hi := (298233213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336869 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336869 / 250000) = 1/(250000 / 336869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13214 : Bounds (74558303 / 250000000) (298233213 / 1000000000) (Real.log (336869 / 250000)) := by
  have h := reflection_log_13214_neg
  have he : Real.log (336869 / 250000) = -Real.log (250000 / 336869) := by
    rw [show ((336869 / 250000) : ℝ) = ((250000 / 336869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13215_neg : (213453679 / 500000000) ≤ -Real.log (163131 / 250000) ∧
    -Real.log (163131 / 250000) ≤ (426907359 / 1000000000) := by
  have h := checkLog_sound (w := (86869 / 413131)) (n := 12)
    (lo := (213453679 / 500000000)) (hi := (426907359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163131) = 1/(163131 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13215 : Bounds (-426907359 / 1000000000) (-213453679 / 500000000) (Real.log (163131 / 250000)) := by
  have h := reflection_log_13215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13216_neg : (15004637 / 50000000) ≤ -Real.log (31250 / 42187) ∧
    -Real.log (31250 / 42187) ≤ (300092741 / 1000000000) := by
  have h := checkLog_sound (w := (10937 / 73437)) (n := 12)
    (lo := (15004637 / 50000000)) (hi := (300092741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42187 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42187 / 31250) = 1/(31250 / 42187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13216 : Bounds (15004637 / 50000000) (300092741 / 1000000000) (Real.log (42187 / 31250)) := by
  have h := reflection_log_13216_neg
  have he : Real.log (42187 / 31250) = -Real.log (31250 / 42187) := by
    rw [show ((42187 / 31250) : ℝ) = ((31250 / 42187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13217_neg : (430758301 / 1000000000) ≤ -Real.log (20313 / 31250) ∧
    -Real.log (20313 / 31250) ≤ (215379151 / 500000000) := by
  have h := checkLog_sound (w := (10937 / 51563)) (n := 12)
    (lo := (430758301 / 1000000000)) (hi := (215379151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20313) = 1/(20313 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13217 : Bounds (-215379151 / 500000000) (-430758301 / 1000000000) (Real.log (20313 / 31250)) := by
  have h := reflection_log_13217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13218_neg : (3266639 / 25000000) ≤ -Real.log (856944531 / 976562500) ∧
    -Real.log (856944531 / 976562500) ≤ (130665561 / 1000000000) := by
  have h := checkLog_sound (w := (119617969 / 1833507031)) (n := 12)
    (lo := (3266639 / 25000000)) (hi := (130665561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 856944531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 856944531) = 1/(856944531 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13218 : Bounds (-130665561 / 1000000000) (-3266639 / 25000000) (Real.log (856944531 / 976562500)) := by
  have h := reflection_log_13218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13219_neg : (25734829 / 200000000) ≤ -Real.log (54953776839 / 62500000000) ∧
    -Real.log (54953776839 / 62500000000) ≤ (64337073 / 500000000) := by
  have h := checkLog_sound (w := (7546223161 / 117453776839)) (n := 12)
    (lo := (25734829 / 200000000)) (hi := (64337073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54953776839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54953776839) = 1/(54953776839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13219 : Bounds (-64337073 / 500000000) (-25734829 / 200000000) (Real.log (54953776839 / 62500000000)) := by
  have h := reflection_log_13219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13220_neg : (725140571 / 1000000000) ≤ -Real.log (500000000000 / 1032510681599) ∧
    -Real.log (500000000000 / 1032510681599) ≤ (725140573 / 1000000000) := by
  have h := checkLog_sound (w := (32510681599 / 2032510681599)) (n := 12)
    (lo := (31993391 / 1000000000)) (hi := (1999587 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032510681599 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032510681599 / 1000000000000) = 1/(500000000000 / 1032510681599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13220 : Bounds (725140571 / 1000000000) (725140573 / 1000000000) (Real.log (1032510681599 / 500000000000)) := by
  have h := reflection_log_13220_neg
  have he : Real.log (1032510681599 / 500000000000) = -Real.log (500000000000 / 1032510681599) := by
    rw [show ((1032510681599 / 500000000000) : ℝ) = ((500000000000 / 1032510681599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13221_neg : (4567819 / 6250000) ≤ -Real.log (125000000000 / 259605917393) ∧
    -Real.log (125000000000 / 259605917393) ≤ (365425521 / 500000000) := by
  have h := checkLog_sound (w := (9605917393 / 509605917393)) (n := 12)
    (lo := (1885193 / 50000000)) (hi := (37703861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259605917393 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259605917393 / 250000000000) = 1/(125000000000 / 259605917393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13221 : Bounds (4567819 / 6250000) (365425521 / 500000000) (Real.log (259605917393 / 125000000000)) := by
  have h := reflection_log_13221_neg
  have he : Real.log (259605917393 / 125000000000) = -Real.log (125000000000 / 259605917393) := by
    rw [show ((259605917393 / 125000000000) : ℝ) = ((125000000000 / 259605917393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13222_neg : (1519738701 / 1000000000) ≤ -Real.log (250000000000 / 1142757660167) ∧
    -Real.log (250000000000 / 1142757660167) ≤ (94983669 / 62500000) := by
  have h := checkLog_sound (w := (142757660167 / 2142757660167)) (n := 12)
    (lo := (133444341 / 1000000000)) (hi := (66722171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142757660167 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1142757660167 / 1000000000000) = 1/(250000000000 / 1142757660167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13222 : Bounds (1519738701 / 1000000000) (94983669 / 62500000) (Real.log (1142757660167 / 250000000000)) := by
  have h := reflection_log_13222_neg
  have he : Real.log (1142757660167 / 250000000000) = -Real.log (250000000000 / 1142757660167) := by
    rw [show ((1142757660167 / 250000000000) : ℝ) = ((250000000000 / 1142757660167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13223_neg : (1529956843 / 1000000000) ≤ -Real.log (100000000000 / 461797752809) ∧
    -Real.log (100000000000 / 461797752809) ≤ (764978423 / 500000000) := by
  have h := checkLog_sound (w := (61797752809 / 861797752809)) (n := 12)
    (lo := (143662483 / 1000000000)) (hi := (35915621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461797752809 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(461797752809 / 400000000000) = 1/(100000000000 / 461797752809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13223 : Bounds (1529956843 / 1000000000) (764978423 / 500000000) (Real.log (461797752809 / 100000000000)) := by
  have h := reflection_log_13223_neg
  have he : Real.log (461797752809 / 100000000000) = -Real.log (100000000000 / 461797752809) := by
    rw [show ((461797752809 / 100000000000) : ℝ) = ((100000000000 / 461797752809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13224_neg : (498955451 / 1000000000) ≤ -Real.log (1000 / 1647) ∧
    -Real.log (1000 / 1647) ≤ (124738863 / 250000000) := by
  have h := checkLog_sound (w := (647 / 2647)) (n := 12)
    (lo := (498955451 / 1000000000)) (hi := (124738863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647 / 1000) = 1/(1000 / 1647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13224 : Bounds (498955451 / 1000000000) (124738863 / 250000000) (Real.log (1647 / 1000)) := by
  have h := reflection_log_13224_neg
  have he : Real.log (1647 / 1000) = -Real.log (1000 / 1647) := by
    rw [show ((1647 / 1000) : ℝ) = ((1000 / 1647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13225_neg : (1041287221 / 1000000000) ≤ -Real.log (353 / 1000) ∧
    -Real.log (353 / 1000) ≤ (1041287223 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 853)) (n := 12)
    (lo := (348140041 / 1000000000)) (hi := (174070021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 353) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 353) = 1/(353 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13225 : Bounds (-1041287223 / 1000000000) (-1041287221 / 1000000000) (Real.log (353 / 1000)) := by
  have h := reflection_log_13225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13226_neg : (64679 / 100000000) ≤ -Real.log (1000000 / 1000647) ∧
    -Real.log (1000000 / 1000647) ≤ (646791 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 2000647)) (n := 12)
    (lo := (64679 / 100000000)) (hi := (646791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000647 / 1000000) = 1/(1000000 / 1000647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13226 : Bounds (64679 / 100000000) (646791 / 1000000000) (Real.log (1000647 / 1000000)) := by
  have h := reflection_log_13226_neg
  have he : Real.log (1000647 / 1000000) = -Real.log (1000000 / 1000647) := by
    rw [show ((1000647 / 1000000) : ℝ) = ((1000000 / 1000647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13227_neg : (647209 / 1000000000) ≤ -Real.log (999353 / 1000000) ∧
    -Real.log (999353 / 1000000) ≤ (64721 / 100000000) := by
  have h := checkLog_sound (w := (647 / 1999353)) (n := 12)
    (lo := (647209 / 1000000000)) (hi := (64721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999353) = 1/(999353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13227 : Bounds (-64721 / 100000000) (-647209 / 1000000000) (Real.log (999353 / 1000000)) := by
  have h := reflection_log_13227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13228_neg : (299661531 / 1000000000) ≤ -Real.log (500000 / 674701) ∧
    -Real.log (500000 / 674701) ≤ (74915383 / 250000000) := by
  have h := checkLog_sound (w := (174701 / 1174701)) (n := 12)
    (lo := (299661531 / 1000000000)) (hi := (74915383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674701 / 500000) = 1/(500000 / 674701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13228 : Bounds (299661531 / 1000000000) (74915383 / 250000000) (Real.log (674701 / 500000)) := by
  have h := reflection_log_13228_neg
  have he : Real.log (674701 / 500000) = -Real.log (500000 / 674701) := by
    rw [show ((674701 / 500000) : ℝ) = ((500000 / 674701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13229_neg : (429863339 / 1000000000) ≤ -Real.log (325299 / 500000) ∧
    -Real.log (325299 / 500000) ≤ (21493167 / 50000000) := by
  have h := checkLog_sound (w := (174701 / 825299)) (n := 12)
    (lo := (429863339 / 1000000000)) (hi := (21493167 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 325299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 325299) = 1/(325299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13229 : Bounds (-21493167 / 50000000) (-429863339 / 1000000000) (Real.log (325299 / 500000)) := by
  have h := reflection_log_13229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13230_neg : (60304717 / 200000000) ≤ -Real.log (1000000 / 1351917) ∧
    -Real.log (1000000 / 1351917) ≤ (150761793 / 500000000) := by
  have h := checkLog_sound (w := (351917 / 2351917)) (n := 12)
    (lo := (60304717 / 200000000)) (hi := (150761793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351917 / 1000000) = 1/(1000000 / 1351917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13230 : Bounds (60304717 / 200000000) (150761793 / 500000000) (Real.log (1351917 / 1000000)) := by
  have h := reflection_log_13230_neg
  have he : Real.log (1351917 / 1000000) = -Real.log (1000000 / 1351917) := by
    rw [show ((1351917 / 1000000) : ℝ) = ((1000000 / 1351917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13231_neg : (54217063 / 125000000) ≤ -Real.log (648083 / 1000000) ∧
    -Real.log (648083 / 1000000) ≤ (86747301 / 200000000) := by
  have h := checkLog_sound (w := (351917 / 1648083)) (n := 12)
    (lo := (54217063 / 125000000)) (hi := (86747301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648083) = 1/(648083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13231 : Bounds (-86747301 / 200000000) (-54217063 / 125000000) (Real.log (648083 / 1000000)) := by
  have h := reflection_log_13231_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13232_neg : (132212919 / 1000000000) ≤ -Real.log (876154425111 / 1000000000000) ∧
    -Real.log (876154425111 / 1000000000000) ≤ (3305323 / 25000000) := by
  have h := checkLog_sound (w := (123845574889 / 1876154425111)) (n := 12)
    (lo := (132212919 / 1000000000)) (hi := (3305323 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 876154425111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 876154425111) = 1/(876154425111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13232 : Bounds (-3305323 / 25000000) (-132212919 / 1000000000) (Real.log (876154425111 / 1000000000000)) := by
  have h := reflection_log_13232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13233_neg : (130201807 / 1000000000) ≤ -Real.log (219479560599 / 250000000000) ∧
    -Real.log (219479560599 / 250000000000) ≤ (8137613 / 62500000) := by
  have h := checkLog_sound (w := (30520439401 / 469479560599)) (n := 12)
    (lo := (130201807 / 1000000000)) (hi := (8137613 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 219479560599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 219479560599) = 1/(219479560599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13233 : Bounds (-8137613 / 62500000) (-130201807 / 1000000000) (Real.log (219479560599 / 250000000000)) := by
  have h := reflection_log_13233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13234_neg : (729524869 / 1000000000) ≤ -Real.log (500000000000 / 1037047454803) ∧
    -Real.log (500000000000 / 1037047454803) ≤ (729524871 / 1000000000) := by
  have h := checkLog_sound (w := (37047454803 / 2037047454803)) (n := 12)
    (lo := (36377689 / 1000000000)) (hi := (3637769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037047454803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1037047454803 / 1000000000000) = 1/(500000000000 / 1037047454803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13234 : Bounds (729524869 / 1000000000) (729524871 / 1000000000) (Real.log (1037047454803 / 500000000000)) := by
  have h := reflection_log_13234_neg
  have he : Real.log (1037047454803 / 500000000000) = -Real.log (500000000000 / 1037047454803) := by
    rw [show ((1037047454803 / 500000000000) : ℝ) = ((500000000000 / 1037047454803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13235_neg : (735260089 / 1000000000) ≤ -Real.log (500000000000 / 1043012237631) ∧
    -Real.log (500000000000 / 1043012237631) ≤ (735260091 / 1000000000) := by
  have h := checkLog_sound (w := (43012237631 / 2043012237631)) (n := 12)
    (lo := (42112909 / 1000000000)) (hi := (4211291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043012237631 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1043012237631 / 1000000000000) = 1/(500000000000 / 1043012237631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13235 : Bounds (735260089 / 1000000000) (735260091 / 1000000000) (Real.log (1043012237631 / 500000000000)) := by
  have h := reflection_log_13235_neg
  have he : Real.log (1043012237631 / 500000000000) = -Real.log (500000000000 / 1043012237631) := by
    rw [show ((1043012237631 / 500000000000) : ℝ) = ((500000000000 / 1043012237631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13236_neg : (1529956843 / 1000000000) ≤ -Real.log (125000000000 / 577247191011) ∧
    -Real.log (125000000000 / 577247191011) ≤ (764978423 / 500000000) := by
  have h := checkLog_sound (w := (77247191011 / 1077247191011)) (n := 12)
    (lo := (143662483 / 1000000000)) (hi := (35915621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577247191011 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(577247191011 / 500000000000) = 1/(125000000000 / 577247191011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13236 : Bounds (1529956843 / 1000000000) (764978423 / 500000000) (Real.log (577247191011 / 125000000000)) := by
  have h := reflection_log_13236_neg
  have he : Real.log (577247191011 / 125000000000) = -Real.log (125000000000 / 577247191011) := by
    rw [show ((577247191011 / 125000000000) : ℝ) = ((125000000000 / 577247191011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13237_neg : (96265167 / 62500000) ≤ -Real.log (250000000000 / 1166430594901) ∧
    -Real.log (250000000000 / 1166430594901) ≤ (61609707 / 40000000) := by
  have h := checkLog_sound (w := (166430594901 / 2166430594901)) (n := 12)
    (lo := (19243539 / 125000000)) (hi := (153948313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166430594901 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1166430594901 / 1000000000000) = 1/(250000000000 / 1166430594901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13237 : Bounds (96265167 / 62500000) (61609707 / 40000000) (Real.log (1166430594901 / 250000000000)) := by
  have h := reflection_log_13237_neg
  have he : Real.log (1166430594901 / 250000000000) = -Real.log (250000000000 / 1166430594901) := by
    rw [show ((1166430594901 / 250000000000) : ℝ) = ((250000000000 / 1166430594901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13238_neg : (500775287 / 1000000000) ≤ -Real.log (20 / 33) ∧
    -Real.log (20 / 33) ≤ (62596911 / 125000000) := by
  have h := checkLog_sound (w := (13 / 53)) (n := 12)
    (lo := (500775287 / 1000000000)) (hi := (62596911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33 / 20) = 1/(20 / 33) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13238 : Bounds (500775287 / 1000000000) (62596911 / 125000000) (Real.log (33 / 20)) := by
  have h := reflection_log_13238_neg
  have he : Real.log (33 / 20) = -Real.log (20 / 33) := by
    rw [show ((33 / 20) : ℝ) = ((20 / 33) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13239_neg : (1049822123 / 1000000000) ≤ -Real.log (7 / 20) ∧
    -Real.log (7 / 20) ≤ (8398577 / 8000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 7) = 1/(7 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13239 : Bounds (-8398577 / 8000000) (-1049822123 / 1000000000) (Real.log (7 / 20)) := by
  have h := reflection_log_13239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13240_neg : (162447 / 250000000) ≤ -Real.log (20000 / 20013) ∧
    -Real.log (20000 / 20013) ≤ (649789 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 40013)) (n := 12)
    (lo := (162447 / 250000000)) (hi := (649789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20013 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20013 / 20000) = 1/(20000 / 20013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13240 : Bounds (162447 / 250000000) (649789 / 1000000000) (Real.log (20013 / 20000)) := by
  have h := reflection_log_13240_neg
  have he : Real.log (20013 / 20000) = -Real.log (20000 / 20013) := by
    rw [show ((20013 / 20000) : ℝ) = ((20000 / 20013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13241_neg : (650211 / 1000000000) ≤ -Real.log (19987 / 20000) ∧
    -Real.log (19987 / 20000) ≤ (162553 / 250000000) := by
  have h := checkLog_sound (w := (13 / 39987)) (n := 12)
    (lo := (650211 / 1000000000)) (hi := (162553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19987) = 1/(19987 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13241 : Bounds (-162553 / 250000000) (-650211 / 1000000000) (Real.log (19987 / 20000)) := by
  have h := reflection_log_13241_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13242_neg : (37636439 / 125000000) ≤ -Real.log (1000000 / 1351333) ∧
    -Real.log (1000000 / 1351333) ≤ (301091513 / 1000000000) := by
  have h := checkLog_sound (w := (351333 / 2351333)) (n := 12)
    (lo := (37636439 / 125000000)) (hi := (301091513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351333 / 1000000) = 1/(1000000 / 1351333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13242 : Bounds (37636439 / 125000000) (301091513 / 1000000000) (Real.log (1351333 / 1000000)) := by
  have h := reflection_log_13242_neg
  have he : Real.log (1351333 / 1000000) = -Real.log (1000000 / 1351333) := by
    rw [show ((1351333 / 1000000) : ℝ) = ((1000000 / 1351333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13243_neg : (432835791 / 1000000000) ≤ -Real.log (648667 / 1000000) ∧
    -Real.log (648667 / 1000000) ≤ (27052237 / 62500000) := by
  have h := checkLog_sound (w := (351333 / 1648667)) (n := 12)
    (lo := (432835791 / 1000000000)) (hi := (27052237 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648667) = 1/(648667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13243 : Bounds (-27052237 / 62500000) (-432835791 / 1000000000) (Real.log (648667 / 1000000)) := by
  have h := reflection_log_13243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13244_neg : (151478039 / 500000000) ≤ -Real.log (200000 / 270771) ∧
    -Real.log (200000 / 270771) ≤ (302956079 / 1000000000) := by
  have h := checkLog_sound (w := (70771 / 470771)) (n := 12)
    (lo := (151478039 / 500000000)) (hi := (302956079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270771 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270771 / 200000) = 1/(200000 / 270771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13244 : Bounds (151478039 / 500000000) (302956079 / 1000000000) (Real.log (270771 / 200000)) := by
  have h := reflection_log_13244_neg
  have he : Real.log (270771 / 200000) = -Real.log (200000 / 270771) := by
    rw [show ((270771 / 200000) : ℝ) = ((200000 / 270771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13245_neg : (218365671 / 500000000) ≤ -Real.log (129229 / 200000) ∧
    -Real.log (129229 / 200000) ≤ (436731343 / 1000000000) := by
  have h := checkLog_sound (w := (70771 / 329229)) (n := 12)
    (lo := (218365671 / 500000000)) (hi := (436731343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129229) = 1/(129229 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13245 : Bounds (-436731343 / 1000000000) (-218365671 / 500000000) (Real.log (129229 / 200000)) := by
  have h := reflection_log_13245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13246_neg : (133775263 / 1000000000) ≤ -Real.log (34991465559 / 40000000000) ∧
    -Real.log (34991465559 / 40000000000) ≤ (4180477 / 31250000) := by
  have h := checkLog_sound (w := (5008534441 / 74991465559)) (n := 12)
    (lo := (133775263 / 1000000000)) (hi := (4180477 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 34991465559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 34991465559) = 1/(34991465559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13246 : Bounds (-4180477 / 31250000) (-133775263 / 1000000000) (Real.log (34991465559 / 40000000000)) := by
  have h := reflection_log_13246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13247_neg : (65872139 / 500000000) ≤ -Real.log (876565123111 / 1000000000000) ∧
    -Real.log (876565123111 / 1000000000000) ≤ (131744279 / 1000000000) := by
  have h := checkLog_sound (w := (123434876889 / 1876565123111)) (n := 12)
    (lo := (65872139 / 500000000)) (hi := (131744279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 876565123111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 876565123111) = 1/(876565123111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13247 : Bounds (-131744279 / 1000000000) (-65872139 / 500000000) (Real.log (876565123111 / 1000000000000)) := by
  have h := reflection_log_13247_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0207 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13248_neg : (733927303 / 1000000000) ≤ -Real.log (500000000000 / 1041623051581) ∧
    -Real.log (500000000000 / 1041623051581) ≤ (146785461 / 200000000) := by
  have h := checkLog_sound (w := (41623051581 / 2041623051581)) (n := 12)
    (lo := (40780123 / 1000000000)) (hi := (10195031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1041623051581 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1041623051581 / 1000000000000) = 1/(500000000000 / 1041623051581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13248 : Bounds (733927303 / 1000000000) (146785461 / 200000000) (Real.log (1041623051581 / 500000000000)) := by
  have h := reflection_log_13248_neg
  have he : Real.log (1041623051581 / 500000000000) = -Real.log (500000000000 / 1041623051581) := by
    rw [show ((1041623051581 / 500000000000) : ℝ) = ((500000000000 / 1041623051581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13249_neg : (36984371 / 50000000) ≤ -Real.log (500000000000 / 1047640235551) ∧
    -Real.log (500000000000 / 1047640235551) ≤ (369843711 / 500000000) := by
  have h := checkLog_sound (w := (47640235551 / 2047640235551)) (n := 12)
    (lo := (581753 / 12500000)) (hi := (46540241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1047640235551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1047640235551 / 1000000000000) = 1/(500000000000 / 1047640235551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13249 : Bounds (36984371 / 50000000) (369843711 / 500000000) (Real.log (1047640235551 / 500000000000)) := by
  have h := reflection_log_13249_neg
  have he : Real.log (1047640235551 / 500000000000) = -Real.log (500000000000 / 1047640235551) := by
    rw [show ((1047640235551 / 500000000000) : ℝ) = ((500000000000 / 1047640235551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13250_neg : (96265167 / 62500000) ≤ -Real.log (500000000000 / 2332861189801) ∧
    -Real.log (500000000000 / 2332861189801) ≤ (61609707 / 40000000) := by
  have h := checkLog_sound (w := (332861189801 / 4332861189801)) (n := 12)
    (lo := (19243539 / 125000000)) (hi := (153948313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2332861189801 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2332861189801 / 2000000000000) = 1/(500000000000 / 2332861189801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13250 : Bounds (96265167 / 62500000) (61609707 / 40000000) (Real.log (2332861189801 / 500000000000)) := by
  have h := reflection_log_13250_neg
  have he : Real.log (2332861189801 / 500000000000) = -Real.log (500000000000 / 2332861189801) := by
    rw [show ((2332861189801 / 500000000000) : ℝ) = ((500000000000 / 2332861189801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13251_neg : (1550597411 / 1000000000) ≤ -Real.log (500000000000 / 2357142857143) ∧
    -Real.log (500000000000 / 2357142857143) ≤ (775298707 / 500000000) := by
  have h := checkLog_sound (w := (357142857143 / 4357142857143)) (n := 12)
    (lo := (164303051 / 1000000000)) (hi := (41075763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2357142857143 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2357142857143 / 2000000000000) = 1/(500000000000 / 2357142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13251 : Bounds (1550597411 / 1000000000) (775298707 / 500000000) (Real.log (2357142857143 / 500000000000)) := by
  have h := reflection_log_13251_neg
  have he : Real.log (2357142857143 / 500000000000) = -Real.log (500000000000 / 2357142857143) := by
    rw [show ((2357142857143 / 500000000000) : ℝ) = ((500000000000 / 2357142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13252_neg : (251295909 / 500000000) ≤ -Real.log (1000 / 1653) ∧
    -Real.log (1000 / 1653) ≤ (502591819 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 2653)) (n := 12)
    (lo := (251295909 / 500000000)) (hi := (502591819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653 / 1000) = 1/(1000 / 1653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13252 : Bounds (251295909 / 500000000) (502591819 / 1000000000) (Real.log (1653 / 1000)) := by
  have h := reflection_log_13252_neg
  have he : Real.log (1653 / 1000) = -Real.log (1000 / 1653) := by
    rw [show ((1653 / 1000) : ℝ) = ((1000 / 1653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13253_neg : (529215249 / 500000000) ≤ -Real.log (347 / 1000) ∧
    -Real.log (347 / 1000) ≤ (2116861 / 2000000) := by
  have h := checkLog_sound (w := (153 / 847)) (n := 12)
    (lo := (182641659 / 500000000)) (hi := (365283319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 347) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 347) = 1/(347 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13253 : Bounds (-2116861 / 2000000) (-529215249 / 500000000) (Real.log (347 / 1000)) := by
  have h := reflection_log_13253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13254_neg : (326393 / 500000000) ≤ -Real.log (1000000 / 1000653) ∧
    -Real.log (1000000 / 1000653) ≤ (652787 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 2000653)) (n := 12)
    (lo := (326393 / 500000000)) (hi := (652787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000653 / 1000000) = 1/(1000000 / 1000653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13254 : Bounds (326393 / 500000000) (652787 / 1000000000) (Real.log (1000653 / 1000000)) := by
  have h := reflection_log_13254_neg
  have he : Real.log (1000653 / 1000000) = -Real.log (1000000 / 1000653) := by
    rw [show ((1000653 / 1000000) : ℝ) = ((1000000 / 1000653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13255_neg : (653213 / 1000000000) ≤ -Real.log (999347 / 1000000) ∧
    -Real.log (999347 / 1000000) ≤ (326607 / 500000000) := by
  have h := checkLog_sound (w := (653 / 1999347)) (n := 12)
    (lo := (653213 / 1000000000)) (hi := (326607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999347) = 1/(999347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13255 : Bounds (-326607 / 500000000) (-653213 / 1000000000) (Real.log (999347 / 1000000)) := by
  have h := reflection_log_13255_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13256_neg : (151261573 / 500000000) ≤ -Real.log (1000000 / 1353269) ∧
    -Real.log (1000000 / 1353269) ≤ (302523147 / 1000000000) := by
  have h := checkLog_sound (w := (353269 / 2353269)) (n := 12)
    (lo := (151261573 / 500000000)) (hi := (302523147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353269 / 1000000) = 1/(1000000 / 1353269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13256 : Bounds (151261573 / 500000000) (302523147 / 1000000000) (Real.log (1353269 / 1000000)) := by
  have h := reflection_log_13256_neg
  have he : Real.log (1353269 / 1000000) = -Real.log (1000000 / 1353269) := by
    rw [show ((1353269 / 1000000) : ℝ) = ((1000000 / 1353269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13257_neg : (108956209 / 250000000) ≤ -Real.log (646731 / 1000000) ∧
    -Real.log (646731 / 1000000) ≤ (435824837 / 1000000000) := by
  have h := checkLog_sound (w := (353269 / 1646731)) (n := 12)
    (lo := (108956209 / 250000000)) (hi := (435824837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646731) = 1/(646731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13257 : Bounds (-435824837 / 1000000000) (-108956209 / 250000000) (Real.log (646731 / 1000000)) := by
  have h := reflection_log_13257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13258_neg : (76097737 / 250000000) ≤ -Real.log (1000000 / 1355799) ∧
    -Real.log (1000000 / 1355799) ≤ (304390949 / 1000000000) := by
  have h := checkLog_sound (w := (355799 / 2355799)) (n := 12)
    (lo := (76097737 / 250000000)) (hi := (304390949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355799 / 1000000) = 1/(1000000 / 1355799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13258 : Bounds (76097737 / 250000000) (304390949 / 1000000000) (Real.log (1355799 / 1000000)) := by
  have h := reflection_log_13258_neg
  have he : Real.log (1355799 / 1000000) = -Real.log (1000000 / 1355799) := by
    rw [show ((1355799 / 1000000) : ℝ) = ((1000000 / 1355799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13259_neg : (439744489 / 1000000000) ≤ -Real.log (644201 / 1000000) ∧
    -Real.log (644201 / 1000000) ≤ (43974449 / 100000000) := by
  have h := checkLog_sound (w := (355799 / 1644201)) (n := 12)
    (lo := (439744489 / 1000000000)) (hi := (43974449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 644201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 644201) = 1/(644201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13259 : Bounds (-43974449 / 100000000) (-439744489 / 1000000000) (Real.log (644201 / 1000000)) := by
  have h := reflection_log_13259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13260_neg : (135353541 / 1000000000) ≤ -Real.log (873407071599 / 1000000000000) ∧
    -Real.log (873407071599 / 1000000000000) ≤ (67676771 / 500000000) := by
  have h := checkLog_sound (w := (126592928401 / 1873407071599)) (n := 12)
    (lo := (135353541 / 1000000000)) (hi := (67676771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 873407071599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 873407071599) = 1/(873407071599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13260 : Bounds (-67676771 / 500000000) (-135353541 / 1000000000) (Real.log (873407071599 / 1000000000000)) := by
  have h := reflection_log_13260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13261_neg : (133301689 / 1000000000) ≤ -Real.log (875201013639 / 1000000000000) ∧
    -Real.log (875201013639 / 1000000000000) ≤ (13330169 / 100000000) := by
  have h := checkLog_sound (w := (124798986361 / 1875201013639)) (n := 12)
    (lo := (133301689 / 1000000000)) (hi := (13330169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 875201013639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 875201013639) = 1/(875201013639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13261 : Bounds (-13330169 / 100000000) (-133301689 / 1000000000) (Real.log (875201013639 / 1000000000000)) := by
  have h := reflection_log_13261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13262_neg : (369173991 / 500000000) ≤ -Real.log (250000000000 / 523118962907) ∧
    -Real.log (250000000000 / 523118962907) ≤ (46146749 / 62500000) := by
  have h := checkLog_sound (w := (23118962907 / 1023118962907)) (n := 12)
    (lo := (22600401 / 500000000)) (hi := (45200803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523118962907 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(523118962907 / 500000000000) = 1/(250000000000 / 523118962907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13262 : Bounds (369173991 / 500000000) (46146749 / 62500000) (Real.log (523118962907 / 250000000000)) := by
  have h := reflection_log_13262_neg
  have he : Real.log (523118962907 / 250000000000) = -Real.log (250000000000 / 523118962907) := by
    rw [show ((523118962907 / 250000000000) : ℝ) = ((250000000000 / 523118962907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13263_neg : (744135437 / 1000000000) ≤ -Real.log (500000000000 / 1052310536619) ∧
    -Real.log (500000000000 / 1052310536619) ≤ (744135439 / 1000000000) := by
  have h := checkLog_sound (w := (52310536619 / 2052310536619)) (n := 12)
    (lo := (50988257 / 1000000000)) (hi := (25494129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1052310536619 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1052310536619 / 1000000000000) = 1/(500000000000 / 1052310536619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13263 : Bounds (744135437 / 1000000000) (744135439 / 1000000000) (Real.log (1052310536619 / 500000000000)) := by
  have h := reflection_log_13263_neg
  have he : Real.log (1052310536619 / 500000000000) = -Real.log (500000000000 / 1052310536619) := by
    rw [show ((1052310536619 / 500000000000) : ℝ) = ((500000000000 / 1052310536619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13264_neg : (1550597411 / 1000000000) ≤ -Real.log (250000000000 / 1178571428571) ∧
    -Real.log (250000000000 / 1178571428571) ≤ (775298707 / 500000000) := by
  have h := checkLog_sound (w := (178571428571 / 2178571428571)) (n := 12)
    (lo := (164303051 / 1000000000)) (hi := (41075763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178571428571 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1178571428571 / 1000000000000) = 1/(250000000000 / 1178571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13264 : Bounds (1550597411 / 1000000000) (775298707 / 500000000) (Real.log (1178571428571 / 250000000000)) := by
  have h := reflection_log_13264_neg
  have he : Real.log (1178571428571 / 250000000000) = -Real.log (250000000000 / 1178571428571) := by
    rw [show ((1178571428571 / 250000000000) : ℝ) = ((250000000000 / 1178571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13265_neg : (390255579 / 250000000) ≤ -Real.log (125000000000 / 595461095101) ∧
    -Real.log (125000000000 / 595461095101) ≤ (1561022319 / 1000000000) := by
  have h := checkLog_sound (w := (95461095101 / 1095461095101)) (n := 12)
    (lo := (43681989 / 250000000)) (hi := (174727957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595461095101 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(595461095101 / 500000000000) = 1/(125000000000 / 595461095101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13265 : Bounds (390255579 / 250000000) (1561022319 / 1000000000) (Real.log (595461095101 / 125000000000)) := by
  have h := reflection_log_13265_neg
  have he : Real.log (595461095101 / 125000000000) = -Real.log (125000000000 / 595461095101) := by
    rw [show ((595461095101 / 125000000000) : ℝ) = ((125000000000 / 595461095101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13266_neg : (100881011 / 200000000) ≤ -Real.log (125 / 207) ∧
    -Real.log (125 / 207) ≤ (7881329 / 15625000) := by
  have h := checkLog_sound (w := (41 / 166)) (n := 12)
    (lo := (100881011 / 200000000)) (hi := (7881329 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207 / 125) = 1/(125 / 207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13266 : Bounds (100881011 / 200000000) (7881329 / 15625000) (Real.log (207 / 125)) := by
  have h := reflection_log_13266_neg
  have he : Real.log (207 / 125) = -Real.log (125 / 207) := by
    rw [show ((207 / 125) : ℝ) = ((125 / 207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13267_neg : (1067113621 / 1000000000) ≤ -Real.log (43 / 125) ∧
    -Real.log (43 / 125) ≤ (1067113623 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 86) = 1/(43 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13267 : Bounds (-1067113623 / 1000000000) (-1067113621 / 1000000000) (Real.log (43 / 125)) := by
  have h := reflection_log_13267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13268_neg : (81973 / 125000000) ≤ -Real.log (62500 / 62541) ∧
    -Real.log (62500 / 62541) ≤ (131157 / 200000000) := by
  have h := checkLog_sound (w := (41 / 125041)) (n := 12)
    (lo := (81973 / 125000000)) (hi := (131157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62541 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62541 / 62500) = 1/(62500 / 62541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13268 : Bounds (81973 / 125000000) (131157 / 200000000) (Real.log (62541 / 62500)) := by
  have h := reflection_log_13268_neg
  have he : Real.log (62541 / 62500) = -Real.log (62500 / 62541) := by
    rw [show ((62541 / 62500) : ℝ) = ((62500 / 62541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13269_neg : (131243 / 200000000) ≤ -Real.log (62459 / 62500) ∧
    -Real.log (62459 / 62500) ≤ (82027 / 125000000) := by
  have h := checkLog_sound (w := (41 / 124959)) (n := 12)
    (lo := (131243 / 200000000)) (hi := (82027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62459) = 1/(62459 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13269 : Bounds (-82027 / 125000000) (-131243 / 200000000) (Real.log (62459 / 62500)) := by
  have h := reflection_log_13269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13270_neg : (303956423 / 1000000000) ≤ -Real.log (100000 / 135521) ∧
    -Real.log (100000 / 135521) ≤ (37994553 / 125000000) := by
  have h := checkLog_sound (w := (35521 / 235521)) (n := 12)
    (lo := (303956423 / 1000000000)) (hi := (37994553 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135521 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135521 / 100000) = 1/(100000 / 135521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13270 : Bounds (303956423 / 1000000000) (37994553 / 125000000) (Real.log (135521 / 100000)) := by
  have h := reflection_log_13270_neg
  have he : Real.log (135521 / 100000) = -Real.log (100000 / 135521) := by
    rw [show ((135521 / 100000) : ℝ) = ((100000 / 135521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13271_neg : (109707649 / 250000000) ≤ -Real.log (64479 / 100000) ∧
    -Real.log (64479 / 100000) ≤ (438830597 / 1000000000) := by
  have h := checkLog_sound (w := (35521 / 164479)) (n := 12)
    (lo := (109707649 / 250000000)) (hi := (438830597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64479) = 1/(64479 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13271 : Bounds (-438830597 / 1000000000) (-109707649 / 250000000) (Real.log (64479 / 100000)) := by
  have h := reflection_log_13271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13272_neg : (76456861 / 250000000) ≤ -Real.log (250000 / 339437) ∧
    -Real.log (250000 / 339437) ≤ (61165489 / 200000000) := by
  have h := checkLog_sound (w := (89437 / 589437)) (n := 12)
    (lo := (76456861 / 250000000)) (hi := (61165489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339437 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339437 / 250000) = 1/(250000 / 339437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13272 : Bounds (76456861 / 250000000) (61165489 / 200000000) (Real.log (339437 / 250000)) := by
  have h := reflection_log_13272_neg
  have he : Real.log (339437 / 250000) = -Real.log (250000 / 339437) := by
    rw [show ((339437 / 250000) : ℝ) = ((250000 / 339437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13273_neg : (864794 / 1953125) ≤ -Real.log (160563 / 250000) ∧
    -Real.log (160563 / 250000) ≤ (442774529 / 1000000000) := by
  have h := checkLog_sound (w := (89437 / 410563)) (n := 12)
    (lo := (864794 / 1953125)) (hi := (442774529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160563) = 1/(160563 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13273 : Bounds (-442774529 / 1000000000) (-864794 / 1953125) (Real.log (160563 / 250000)) := by
  have h := reflection_log_13273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13274_neg : (34236771 / 250000000) ≤ -Real.log (54501023031 / 62500000000) ∧
    -Real.log (54501023031 / 62500000000) ≤ (27389417 / 200000000) := by
  have h := checkLog_sound (w := (7998976969 / 117001023031)) (n := 12)
    (lo := (34236771 / 250000000)) (hi := (27389417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54501023031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54501023031) = 1/(54501023031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13274 : Bounds (-27389417 / 200000000) (-34236771 / 250000000) (Real.log (54501023031 / 62500000000)) := by
  have h := reflection_log_13274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13275_neg : (33718543 / 250000000) ≤ -Real.log (8738258559 / 10000000000) ∧
    -Real.log (8738258559 / 10000000000) ≤ (134874173 / 1000000000) := by
  have h := checkLog_sound (w := (1261741441 / 18738258559)) (n := 12)
    (lo := (33718543 / 250000000)) (hi := (134874173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8738258559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8738258559) = 1/(8738258559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13275 : Bounds (-134874173 / 1000000000) (-33718543 / 250000000) (Real.log (8738258559 / 10000000000)) := by
  have h := reflection_log_13275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13276_neg : (742787019 / 1000000000) ≤ -Real.log (100000000000 / 210178507731) ∧
    -Real.log (100000000000 / 210178507731) ≤ (742787021 / 1000000000) := by
  have h := checkLog_sound (w := (10178507731 / 410178507731)) (n := 12)
    (lo := (49639839 / 1000000000)) (hi := (310249 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210178507731 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210178507731 / 200000000000) = 1/(100000000000 / 210178507731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13276 : Bounds (742787019 / 1000000000) (742787021 / 1000000000) (Real.log (210178507731 / 100000000000)) := by
  have h := reflection_log_13276_neg
  have he : Real.log (210178507731 / 100000000000) = -Real.log (100000000000 / 210178507731) := by
    rw [show ((210178507731 / 100000000000) : ℝ) = ((100000000000 / 210178507731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13277_neg : (748601973 / 1000000000) ≤ -Real.log (250000000000 / 528510615771) ∧
    -Real.log (250000000000 / 528510615771) ≤ (29944079 / 40000000) := by
  have h := checkLog_sound (w := (28510615771 / 1028510615771)) (n := 12)
    (lo := (55454793 / 1000000000)) (hi := (27727397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528510615771 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(528510615771 / 500000000000) = 1/(250000000000 / 528510615771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13277 : Bounds (748601973 / 1000000000) (29944079 / 40000000) (Real.log (528510615771 / 250000000000)) := by
  have h := reflection_log_13277_neg
  have he : Real.log (528510615771 / 250000000000) = -Real.log (250000000000 / 528510615771) := by
    rw [show ((528510615771 / 250000000000) : ℝ) = ((250000000000 / 528510615771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13278_neg : (390255579 / 250000000) ≤ -Real.log (500000000000 / 2381844380403) ∧
    -Real.log (500000000000 / 2381844380403) ≤ (1561022319 / 1000000000) := by
  have h := checkLog_sound (w := (381844380403 / 4381844380403)) (n := 12)
    (lo := (43681989 / 250000000)) (hi := (174727957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2381844380403 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2381844380403 / 2000000000000) = 1/(500000000000 / 2381844380403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13278 : Bounds (390255579 / 250000000) (1561022319 / 1000000000) (Real.log (2381844380403 / 500000000000)) := by
  have h := reflection_log_13278_neg
  have he : Real.log (2381844380403 / 500000000000) = -Real.log (500000000000 / 2381844380403) := by
    rw [show ((2381844380403 / 500000000000) : ℝ) = ((500000000000 / 2381844380403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13279_neg : (392879669 / 250000000) ≤ -Real.log (500000000000 / 2406976744187) ∧
    -Real.log (500000000000 / 2406976744187) ≤ (1571518679 / 1000000000) := by
  have h := checkLog_sound (w := (406976744187 / 4406976744187)) (n := 12)
    (lo := (46306079 / 250000000)) (hi := (185224317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2406976744187 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2406976744187 / 2000000000000) = 1/(500000000000 / 2406976744187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13279 : Bounds (392879669 / 250000000) (1571518679 / 1000000000) (Real.log (2406976744187 / 500000000000)) := by
  have h := reflection_log_13279_neg
  have he : Real.log (2406976744187 / 500000000000) = -Real.log (500000000000 / 2406976744187) := by
    rw [show ((2406976744187 / 500000000000) : ℝ) = ((500000000000 / 2406976744187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13280_neg : (506215011 / 1000000000) ≤ -Real.log (1000 / 1659) ∧
    -Real.log (1000 / 1659) ≤ (126553753 / 250000000) := by
  have h := checkLog_sound (w := (659 / 2659)) (n := 12)
    (lo := (506215011 / 1000000000)) (hi := (126553753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659 / 1000) = 1/(1000 / 1659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13280 : Bounds (506215011 / 1000000000) (126553753 / 250000000) (Real.log (1659 / 1000)) := by
  have h := reflection_log_13280_neg
  have he : Real.log (1659 / 1000) = -Real.log (1000 / 1659) := by
    rw [show ((1659 / 1000) : ℝ) = ((1000 / 1659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13281_neg : (1075872801 / 1000000000) ≤ -Real.log (341 / 1000) ∧
    -Real.log (341 / 1000) ≤ (1075872803 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 841)) (n := 12)
    (lo := (382725621 / 1000000000)) (hi := (191362811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 341) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 341) = 1/(341 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13281 : Bounds (-1075872803 / 1000000000) (-1075872801 / 1000000000) (Real.log (341 / 1000)) := by
  have h := reflection_log_13281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13282_neg : (329391 / 500000000) ≤ -Real.log (1000000 / 1000659) ∧
    -Real.log (1000000 / 1000659) ≤ (658783 / 1000000000) := by
  have h := checkLog_sound (w := (659 / 2000659)) (n := 12)
    (lo := (329391 / 500000000)) (hi := (658783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000659 / 1000000) = 1/(1000000 / 1000659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13282 : Bounds (329391 / 500000000) (658783 / 1000000000) (Real.log (1000659 / 1000000)) := by
  have h := reflection_log_13282_neg
  have he : Real.log (1000659 / 1000000) = -Real.log (1000000 / 1000659) := by
    rw [show ((1000659 / 1000000) : ℝ) = ((1000000 / 1000659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13283_neg : (659217 / 1000000000) ≤ -Real.log (999341 / 1000000) ∧
    -Real.log (999341 / 1000000) ≤ (329609 / 500000000) := by
  have h := checkLog_sound (w := (659 / 1999341)) (n := 12)
    (lo := (659217 / 1000000000)) (hi := (329609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999341) = 1/(999341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13283 : Bounds (-329609 / 500000000) (-659217 / 1000000000) (Real.log (999341 / 1000000)) := by
  have h := reflection_log_13283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13284_neg : (30539207 / 100000000) ≤ -Real.log (1000000 / 1357157) ∧
    -Real.log (1000000 / 1357157) ≤ (305392071 / 1000000000) := by
  have h := checkLog_sound (w := (357157 / 2357157)) (n := 12)
    (lo := (30539207 / 100000000)) (hi := (305392071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357157 / 1000000) = 1/(1000000 / 1357157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13284 : Bounds (30539207 / 100000000) (305392071 / 1000000000) (Real.log (1357157 / 1000000)) := by
  have h := reflection_log_13284_neg
  have he : Real.log (1357157 / 1000000) = -Real.log (1000000 / 1357157) := by
    rw [show ((1357157 / 1000000) : ℝ) = ((1000000 / 1357157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13285_neg : (13807961 / 31250000) ≤ -Real.log (642843 / 1000000) ∧
    -Real.log (642843 / 1000000) ≤ (441854753 / 1000000000) := by
  have h := checkLog_sound (w := (357157 / 1642843)) (n := 12)
    (lo := (13807961 / 31250000)) (hi := (441854753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642843) = 1/(642843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13285 : Bounds (-441854753 / 1000000000) (-13807961 / 31250000) (Real.log (642843 / 1000000)) := by
  have h := reflection_log_13285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13286_neg : (153632779 / 500000000) ≤ -Real.log (500000 / 679851) ∧
    -Real.log (500000 / 679851) ≤ (307265559 / 1000000000) := by
  have h := checkLog_sound (w := (179851 / 1179851)) (n := 12)
    (lo := (153632779 / 500000000)) (hi := (307265559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679851 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679851 / 500000) = 1/(500000 / 679851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13286 : Bounds (153632779 / 500000000) (307265559 / 1000000000) (Real.log (679851 / 500000)) := by
  have h := reflection_log_13286_neg
  have he : Real.log (679851 / 500000) = -Real.log (500000 / 679851) := by
    rw [show ((679851 / 500000) : ℝ) = ((500000 / 679851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13287_neg : (89164317 / 200000000) ≤ -Real.log (320149 / 500000) ∧
    -Real.log (320149 / 500000) ≤ (222910793 / 500000000) := by
  have h := checkLog_sound (w := (179851 / 820149)) (n := 12)
    (lo := (89164317 / 200000000)) (hi := (222910793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320149) = 1/(320149 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13287 : Bounds (-222910793 / 500000000) (-89164317 / 200000000) (Real.log (320149 / 500000)) := by
  have h := reflection_log_13287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13288_neg : (138556027 / 1000000000) ≤ -Real.log (217653617799 / 250000000000) ∧
    -Real.log (217653617799 / 250000000000) ≤ (34639007 / 250000000) := by
  have h := checkLog_sound (w := (32346382201 / 467653617799)) (n := 12)
    (lo := (138556027 / 1000000000)) (hi := (34639007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 217653617799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 217653617799) = 1/(217653617799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13288 : Bounds (-34639007 / 250000000) (-138556027 / 1000000000) (Real.log (217653617799 / 250000000000)) := by
  have h := reflection_log_13288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13289_neg : (136462681 / 1000000000) ≤ -Real.log (872438877351 / 1000000000000) ∧
    -Real.log (872438877351 / 1000000000000) ≤ (68231341 / 500000000) := by
  have h := checkLog_sound (w := (127561122649 / 1872438877351)) (n := 12)
    (lo := (136462681 / 1000000000)) (hi := (68231341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 872438877351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 872438877351) = 1/(872438877351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13289 : Bounds (-68231341 / 500000000) (-136462681 / 1000000000) (Real.log (872438877351 / 1000000000000)) := by
  have h := reflection_log_13289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13290_neg : (373623411 / 500000000) ≤ -Real.log (50000000000 / 105558977853) ∧
    -Real.log (50000000000 / 105558977853) ≤ (93405853 / 125000000) := by
  have h := checkLog_sound (w := (5558977853 / 205558977853)) (n := 12)
    (lo := (27049821 / 500000000)) (hi := (54099643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105558977853 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(105558977853 / 100000000000) = 1/(50000000000 / 105558977853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13290 : Bounds (373623411 / 500000000) (93405853 / 125000000) (Real.log (105558977853 / 50000000000)) := by
  have h := reflection_log_13290_neg
  have he : Real.log (105558977853 / 50000000000) = -Real.log (50000000000 / 105558977853) := by
    rw [show ((105558977853 / 50000000000) : ℝ) = ((50000000000 / 105558977853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13291_neg : (753087143 / 1000000000) ≤ -Real.log (500000000000 / 1061772799541) ∧
    -Real.log (500000000000 / 1061772799541) ≤ (150617429 / 200000000) := by
  have h := checkLog_sound (w := (61772799541 / 2061772799541)) (n := 12)
    (lo := (59939963 / 1000000000)) (hi := (14984991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061772799541 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061772799541 / 1000000000000) = 1/(500000000000 / 1061772799541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13291 : Bounds (753087143 / 1000000000) (150617429 / 200000000) (Real.log (1061772799541 / 500000000000)) := by
  have h := reflection_log_13291_neg
  have he : Real.log (1061772799541 / 500000000000) = -Real.log (500000000000 / 1061772799541) := by
    rw [show ((1061772799541 / 500000000000) : ℝ) = ((500000000000 / 1061772799541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13292_neg : (392879669 / 250000000) ≤ -Real.log (250000000000 / 1203488372093) ∧
    -Real.log (250000000000 / 1203488372093) ≤ (1571518679 / 1000000000) := by
  have h := checkLog_sound (w := (203488372093 / 2203488372093)) (n := 12)
    (lo := (46306079 / 250000000)) (hi := (185224317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203488372093 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1203488372093 / 1000000000000) = 1/(250000000000 / 1203488372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13292 : Bounds (392879669 / 250000000) (1571518679 / 1000000000) (Real.log (1203488372093 / 250000000000)) := by
  have h := reflection_log_13292_neg
  have he : Real.log (1203488372093 / 250000000000) = -Real.log (250000000000 / 1203488372093) := by
    rw [show ((1203488372093 / 250000000000) : ℝ) = ((250000000000 / 1203488372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13293_neg : (1582087811 / 1000000000) ≤ -Real.log (500000000000 / 2432551319649) ∧
    -Real.log (500000000000 / 2432551319649) ≤ (791043907 / 500000000) := by
  have h := checkLog_sound (w := (432551319649 / 4432551319649)) (n := 12)
    (lo := (195793451 / 1000000000)) (hi := (48948363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2432551319649 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2432551319649 / 2000000000000) = 1/(500000000000 / 2432551319649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13293 : Bounds (1582087811 / 1000000000) (791043907 / 500000000) (Real.log (2432551319649 / 500000000000)) := by
  have h := reflection_log_13293_neg
  have he : Real.log (2432551319649 / 500000000000) = -Real.log (500000000000 / 2432551319649) := by
    rw [show ((2432551319649 / 500000000000) : ℝ) = ((500000000000 / 2432551319649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13294_neg : (7937839 / 15625000) ≤ -Real.log (500 / 831) ∧
    -Real.log (500 / 831) ≤ (508021697 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1331)) (n := 12)
    (lo := (7937839 / 15625000)) (hi := (508021697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831 / 500) = 1/(500 / 831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13294 : Bounds (7937839 / 15625000) (508021697 / 1000000000) (Real.log (831 / 500)) := by
  have h := reflection_log_13294_neg
  have he : Real.log (831 / 500) = -Real.log (500 / 831) := by
    rw [show ((831 / 500) : ℝ) = ((500 / 831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13295_neg : (542354691 / 500000000) ≤ -Real.log (169 / 500) ∧
    -Real.log (169 / 500) ≤ (135588673 / 125000000) := by
  have h := checkLog_sound (w := (81 / 419)) (n := 12)
    (lo := (195781101 / 500000000)) (hi := (391562203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 169) = 1/(169 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13295 : Bounds (-135588673 / 125000000) (-542354691 / 500000000) (Real.log (169 / 500)) := by
  have h := reflection_log_13295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13296_neg : (33089 / 50000000) ≤ -Real.log (500000 / 500331) ∧
    -Real.log (500000 / 500331) ≤ (661781 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1000331)) (n := 12)
    (lo := (33089 / 50000000)) (hi := (661781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500331 / 500000) = 1/(500000 / 500331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13296 : Bounds (33089 / 50000000) (661781 / 1000000000) (Real.log (500331 / 500000)) := by
  have h := reflection_log_13296_neg
  have he : Real.log (500331 / 500000) = -Real.log (500000 / 500331) := by
    rw [show ((500331 / 500000) : ℝ) = ((500000 / 500331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13297_neg : (662219 / 1000000000) ≤ -Real.log (499669 / 500000) ∧
    -Real.log (499669 / 500000) ≤ (33111 / 50000000) := by
  have h := checkLog_sound (w := (331 / 999669)) (n := 12)
    (lo := (662219 / 1000000000)) (hi := (33111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499669) = 1/(499669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13297 : Bounds (-33111 / 50000000) (-662219 / 1000000000) (Real.log (499669 / 500000)) := by
  have h := reflection_log_13297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13298_neg : (306830073 / 1000000000) ≤ -Real.log (100000 / 135911) ∧
    -Real.log (100000 / 135911) ≤ (153415037 / 500000000) := by
  have h := checkLog_sound (w := (35911 / 235911)) (n := 12)
    (lo := (306830073 / 1000000000)) (hi := (153415037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135911 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135911 / 100000) = 1/(100000 / 135911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13298 : Bounds (306830073 / 1000000000) (153415037 / 500000000) (Real.log (135911 / 100000)) := by
  have h := reflection_log_13298_neg
  have he : Real.log (135911 / 100000) = -Real.log (100000 / 135911) := by
    rw [show ((135911 / 100000) : ℝ) = ((100000 / 135911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13299_neg : (444897443 / 1000000000) ≤ -Real.log (64089 / 100000) ∧
    -Real.log (64089 / 100000) ≤ (111224361 / 250000000) := by
  have h := checkLog_sound (w := (35911 / 164089)) (n := 12)
    (lo := (444897443 / 1000000000)) (hi := (111224361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64089) = 1/(64089 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13299 : Bounds (-111224361 / 250000000) (-444897443 / 1000000000) (Real.log (64089 / 100000)) := by
  have h := reflection_log_13299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13300_neg : (77176503 / 250000000) ≤ -Real.log (500000 / 680831) ∧
    -Real.log (500000 / 680831) ≤ (308706013 / 1000000000) := by
  have h := checkLog_sound (w := (180831 / 1180831)) (n := 12)
    (lo := (77176503 / 250000000)) (hi := (308706013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680831 / 500000) = 1/(500000 / 680831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13300 : Bounds (77176503 / 250000000) (308706013 / 1000000000) (Real.log (680831 / 500000)) := by
  have h := reflection_log_13300_neg
  have he : Real.log (680831 / 500000) = -Real.log (500000 / 680831) := by
    rw [show ((680831 / 500000) : ℝ) = ((500000 / 680831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13301_neg : (89777471 / 200000000) ≤ -Real.log (319169 / 500000) ∧
    -Real.log (319169 / 500000) ≤ (112221839 / 250000000) := by
  have h := checkLog_sound (w := (180831 / 819169)) (n := 12)
    (lo := (89777471 / 200000000)) (hi := (112221839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 319169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 319169) = 1/(319169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13301 : Bounds (-112221839 / 250000000) (-89777471 / 200000000) (Real.log (319169 / 500000)) := by
  have h := reflection_log_13301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13302_neg : (70090671 / 500000000) ≤ -Real.log (217300149439 / 250000000000) ∧
    -Real.log (217300149439 / 250000000000) ≤ (140181343 / 1000000000) := by
  have h := checkLog_sound (w := (32699850561 / 467300149439)) (n := 12)
    (lo := (70090671 / 500000000)) (hi := (140181343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 217300149439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 217300149439) = 1/(217300149439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13302 : Bounds (-140181343 / 1000000000) (-70090671 / 500000000) (Real.log (217300149439 / 250000000000)) := by
  have h := reflection_log_13302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13303_neg : (138067369 / 1000000000) ≤ -Real.log (8710400079 / 10000000000) ∧
    -Real.log (8710400079 / 10000000000) ≤ (13806737 / 100000000) := by
  have h := checkLog_sound (w := (1289599921 / 18710400079)) (n := 12)
    (lo := (138067369 / 1000000000)) (hi := (13806737 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8710400079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8710400079) = 1/(8710400079 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13303 : Bounds (-13806737 / 100000000) (-138067369 / 1000000000) (Real.log (8710400079 / 10000000000)) := by
  have h := reflection_log_13303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13304_neg : (187931879 / 250000000) ≤ -Real.log (500000000000 / 1060330165863) ∧
    -Real.log (500000000000 / 1060330165863) ≤ (375863759 / 500000000) := by
  have h := checkLog_sound (w := (60330165863 / 2060330165863)) (n := 12)
    (lo := (3661271 / 62500000)) (hi := (58580337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060330165863 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1060330165863 / 1000000000000) = 1/(500000000000 / 1060330165863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13304 : Bounds (187931879 / 250000000) (375863759 / 500000000) (Real.log (1060330165863 / 500000000000)) := by
  have h := reflection_log_13304_neg
  have he : Real.log (1060330165863 / 500000000000) = -Real.log (500000000000 / 1060330165863) := by
    rw [show ((1060330165863 / 500000000000) : ℝ) = ((500000000000 / 1060330165863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13305_neg : (757593367 / 1000000000) ≤ -Real.log (500000000000 / 1066568181747) ∧
    -Real.log (500000000000 / 1066568181747) ≤ (757593369 / 1000000000) := by
  have h := checkLog_sound (w := (66568181747 / 2066568181747)) (n := 12)
    (lo := (64446187 / 1000000000)) (hi := (16111547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066568181747 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1066568181747 / 1000000000000) = 1/(500000000000 / 1066568181747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13305 : Bounds (757593367 / 1000000000) (757593369 / 1000000000) (Real.log (1066568181747 / 500000000000)) := by
  have h := reflection_log_13305_neg
  have he : Real.log (1066568181747 / 500000000000) = -Real.log (500000000000 / 1066568181747) := by
    rw [show ((1066568181747 / 500000000000) : ℝ) = ((500000000000 / 1066568181747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13306_neg : (1582087811 / 1000000000) ≤ -Real.log (15625000000 / 76017228739) ∧
    -Real.log (15625000000 / 76017228739) ≤ (791043907 / 500000000) := by
  have h := checkLog_sound (w := (13517228739 / 138517228739)) (n := 12)
    (lo := (195793451 / 1000000000)) (hi := (48948363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76017228739 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(76017228739 / 62500000000) = 1/(15625000000 / 76017228739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13306 : Bounds (1582087811 / 1000000000) (791043907 / 500000000) (Real.log (76017228739 / 15625000000)) := by
  have h := reflection_log_13306_neg
  have he : Real.log (76017228739 / 15625000000) = -Real.log (15625000000 / 76017228739) := by
    rw [show ((76017228739 / 15625000000) : ℝ) = ((15625000000 / 76017228739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13307_neg : (796365539 / 500000000) ≤ -Real.log (500000000000 / 2458579881657) ∧
    -Real.log (500000000000 / 2458579881657) ≤ (1592731081 / 1000000000) := by
  have h := checkLog_sound (w := (458579881657 / 4458579881657)) (n := 12)
    (lo := (103218359 / 500000000)) (hi := (206436719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2458579881657 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2458579881657 / 2000000000000) = 1/(500000000000 / 2458579881657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13307 : Bounds (796365539 / 500000000) (1592731081 / 1000000000) (Real.log (2458579881657 / 500000000000)) := by
  have h := reflection_log_13307_neg
  have he : Real.log (2458579881657 / 500000000000) = -Real.log (500000000000 / 2458579881657) := by
    rw [show ((2458579881657 / 500000000000) : ℝ) = ((500000000000 / 2458579881657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13308_neg : (509825123 / 1000000000) ≤ -Real.log (200 / 333) ∧
    -Real.log (200 / 333) ≤ (127456281 / 250000000) := by
  have h := checkLog_sound (w := (133 / 533)) (n := 12)
    (lo := (509825123 / 1000000000)) (hi := (127456281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 200) = 1/(200 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13308 : Bounds (509825123 / 1000000000) (127456281 / 250000000) (Real.log (333 / 200)) := by
  have h := reflection_log_13308_neg
  have he : Real.log (333 / 200) = -Real.log (200 / 333) := by
    rw [show ((333 / 200) : ℝ) = ((200 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13309_neg : (546812373 / 500000000) ≤ -Real.log (67 / 200) ∧
    -Real.log (67 / 200) ≤ (273406187 / 250000000) := by
  have h := checkLog_sound (w := (33 / 167)) (n := 12)
    (lo := (200238783 / 500000000)) (hi := (400477567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 67) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 67) = 1/(67 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13309 : Bounds (-273406187 / 250000000) (-546812373 / 500000000) (Real.log (67 / 200)) := by
  have h := reflection_log_13309_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13310_neg : (332389 / 500000000) ≤ -Real.log (200000 / 200133) ∧
    -Real.log (200000 / 200133) ≤ (664779 / 1000000000) := by
  have h := checkLog_sound (w := (133 / 400133)) (n := 12)
    (lo := (332389 / 500000000)) (hi := (664779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200133 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200133 / 200000) = 1/(200000 / 200133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13310 : Bounds (332389 / 500000000) (664779 / 1000000000) (Real.log (200133 / 200000)) := by
  have h := reflection_log_13310_neg
  have he : Real.log (200133 / 200000) = -Real.log (200000 / 200133) := by
    rw [show ((200133 / 200000) : ℝ) = ((200000 / 200133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13311_neg : (665221 / 1000000000) ≤ -Real.log (199867 / 200000) ∧
    -Real.log (199867 / 200000) ≤ (332611 / 500000000) := by
  have h := checkLog_sound (w := (133 / 399867)) (n := 12)
    (lo := (665221 / 1000000000)) (hi := (332611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199867) = 1/(199867 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13311 : Bounds (-332611 / 500000000) (-665221 / 1000000000) (Real.log (199867 / 200000)) := by
  have h := reflection_log_13311_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


