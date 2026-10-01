-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0036Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0036Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:41:03.173628+00:00
-- url     : https://prove2.me/theorems/f95b5966-e7a3-45fd-b829-6ca6f8e207ee
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0037Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0037Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0038Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0039Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0037Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0038Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0039Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0037Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0038Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0039Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0036Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0037Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0038Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0039Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0036Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0036
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

theorem reflection_log_1_neg : (192870301 / 500000000) ≤ -Real.log (512 / 753) ∧
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


theorem reflection_log_1 : Bounds (192870301 / 500000000) (385740603 / 1000000000) (Real.log (753 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (753 / 512) = -Real.log (512 / 753) := by
    rw [show ((753 / 512) : ℝ) = ((512 / 753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (159051451 / 250000000) ≤ -Real.log (271 / 512) ∧
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


theorem reflection_log_2 : Bounds (-127241161 / 200000000) (-159051451 / 250000000) (Real.log (271 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24058967 / 62500000) ≤ -Real.log (1280 / 1881) ∧
    -Real.log (1280 / 1881) ≤ (384943473 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 3161)) (n := 12)
    (lo := (24058967 / 62500000)) (hi := (384943473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881 / 1280) = 1/(1280 / 1881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24058967 / 62500000) (384943473 / 1000000000) (Real.log (1881 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1881 / 1280) = -Real.log (1280 / 1881) := by
    rw [show ((1881 / 1280) : ℝ) = ((1280 / 1881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (633994229 / 1000000000) ≤ -Real.log (679 / 1280) ∧
    -Real.log (679 / 1280) ≤ (63399423 / 100000000) := by
  have h := checkLog_sound (w := (601 / 1959)) (n := 12)
    (lo := (633994229 / 1000000000)) (hi := (63399423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 679) = 1/(679 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63399423 / 100000000) (-633994229 / 1000000000) (Real.log (679 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
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


theorem reflection_log_5 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
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


theorem reflection_log_6 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10346947 / 15625000) ≤ -Real.log (640 / 1241) ∧
    -Real.log (640 / 1241) ≤ (662204609 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 1881)) (n := 12)
    (lo := (10346947 / 15625000)) (hi := (662204609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241 / 640) = 1/(640 / 1241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10346947 / 15625000) (662204609 / 1000000000) (Real.log (1241 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1241 / 640) = -Real.log (640 / 1241) := by
    rw [show ((1241 / 640) : ℝ) = ((640 / 1241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2797906527 / 1000000000) ≤ -Real.log (39 / 640) ∧
    -Real.log (39 / 640) ≤ (699476633 / 250000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 39) = 1/(39 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-699476633 / 250000000) (-2797906527 / 1000000000) (Real.log (39 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (535951703 / 1000000000) ≤ -Real.log (500000 / 854537) ∧
    -Real.log (500000 / 854537) ≤ (66993963 / 125000000) := by
  have h := checkLog_sound (w := (354537 / 1354537)) (n := 12)
    (lo := (535951703 / 1000000000)) (hi := (66993963 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854537 / 500000) = 1/(500000 / 854537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (535951703 / 1000000000) (66993963 / 125000000) (Real.log (854537 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (854537 / 500000) = -Real.log (500000 / 854537) := by
    rw [show ((854537 / 500000) : ℝ) = ((500000 / 854537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1234686339 / 1000000000) ≤ -Real.log (145463 / 500000) ∧
    -Real.log (145463 / 500000) ≤ (1234686341 / 1000000000) := by
  have h := checkLog_sound (w := (104537 / 395463)) (n := 12)
    (lo := (541539159 / 1000000000)) (hi := (13538479 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 145463) = 1/(145463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1234686341 / 1000000000) (-1234686339 / 1000000000) (Real.log (145463 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (537295387 / 1000000000) ≤ -Real.log (250000 / 427843) ∧
    -Real.log (250000 / 427843) ≤ (134323847 / 250000000) := by
  have h := checkLog_sound (w := (177843 / 677843)) (n := 12)
    (lo := (537295387 / 1000000000)) (hi := (134323847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427843 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427843 / 250000) = 1/(250000 / 427843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (537295387 / 1000000000) (134323847 / 250000000) (Real.log (427843 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (427843 / 250000) = -Real.log (250000 / 427843) := by
    rw [show ((427843 / 250000) : ℝ) = ((250000 / 427843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (155327077 / 125000000) ≤ -Real.log (72157 / 250000) ∧
    -Real.log (72157 / 250000) ≤ (621308309 / 500000000) := by
  have h := checkLog_sound (w := (52843 / 197157)) (n := 12)
    (lo := (137367359 / 250000000)) (hi := (549469437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 72157) = 1/(72157 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-621308309 / 500000000) (-155327077 / 125000000) (Real.log (72157 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (22904301 / 50000000) ≤ -Real.log (200000 / 316209) ∧
    -Real.log (200000 / 316209) ≤ (458086021 / 1000000000) := by
  have h := checkLog_sound (w := (116209 / 516209)) (n := 12)
    (lo := (22904301 / 50000000)) (hi := (458086021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316209 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316209 / 200000) = 1/(200000 / 316209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (22904301 / 50000000) (458086021 / 1000000000) (Real.log (316209 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (316209 / 200000) = -Real.log (200000 / 316209) := by
    rw [show ((316209 / 200000) : ℝ) = ((200000 / 316209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (434995881 / 500000000) ≤ -Real.log (83791 / 200000) ∧
    -Real.log (83791 / 200000) ≤ (217497941 / 250000000) := by
  have h := checkLog_sound (w := (16209 / 183791)) (n := 12)
    (lo := (88422291 / 500000000)) (hi := (176844583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83791) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 83791) = 1/(83791 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-217497941 / 250000000) (-434995881 / 500000000) (Real.log (83791 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14363793 / 31250000) ≤ -Real.log (500000 / 791753) ∧
    -Real.log (500000 / 791753) ≤ (459641377 / 1000000000) := by
  have h := checkLog_sound (w := (291753 / 1291753)) (n := 12)
    (lo := (14363793 / 31250000)) (hi := (459641377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791753 / 500000) = 1/(500000 / 791753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14363793 / 31250000) (459641377 / 1000000000) (Real.log (791753 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (791753 / 500000) = -Real.log (500000 / 791753) := by
    rw [show ((791753 / 500000) : ℝ) = ((500000 / 791753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (437941611 / 500000000) ≤ -Real.log (208247 / 500000) ∧
    -Real.log (208247 / 500000) ≤ (109485403 / 125000000) := by
  have h := checkLog_sound (w := (41753 / 458247)) (n := 12)
    (lo := (91368021 / 500000000)) (hi := (182736043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208247) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 208247) = 1/(208247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-109485403 / 125000000) (-437941611 / 500000000) (Real.log (208247 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1770638041 / 1000000000) ≤ -Real.log (20000000000 / 117492008277) ∧
    -Real.log (20000000000 / 117492008277) ≤ (442659511 / 250000000) := by
  have h := checkLog_sound (w := (37492008277 / 197492008277)) (n := 12)
    (lo := (384343681 / 1000000000)) (hi := (192171841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117492008277 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(117492008277 / 80000000000) = 1/(20000000000 / 117492008277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1770638041 / 1000000000) (442659511 / 250000000) (Real.log (117492008277 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (117492008277 / 20000000000) = -Real.log (20000000000 / 117492008277) := by
    rw [show ((117492008277 / 20000000000) : ℝ) = ((20000000000 / 117492008277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (444978001 / 250000000) ≤ -Real.log (125000000000 / 741166830661) ∧
    -Real.log (125000000000 / 741166830661) ≤ (1779912007 / 1000000000) := by
  have h := checkLog_sound (w := (241166830661 / 1241166830661)) (n := 12)
    (lo := (98404411 / 250000000)) (hi := (78723529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741166830661 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(741166830661 / 500000000000) = 1/(125000000000 / 741166830661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (444978001 / 250000000) (1779912007 / 1000000000) (Real.log (741166830661 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (741166830661 / 125000000000) = -Real.log (125000000000 / 741166830661) := by
    rw [show ((741166830661 / 125000000000) : ℝ) = ((125000000000 / 741166830661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1328077783 / 1000000000) ≤ -Real.log (125000000000 / 471722798391) ∧
    -Real.log (125000000000 / 471722798391) ≤ (265615557 / 200000000) := by
  have h := checkLog_sound (w := (221722798391 / 721722798391)) (n := 12)
    (lo := (634930603 / 1000000000)) (hi := (158732651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471722798391 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(471722798391 / 250000000000) = 1/(125000000000 / 471722798391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1328077783 / 1000000000) (265615557 / 200000000) (Real.log (471722798391 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (471722798391 / 125000000000) = -Real.log (125000000000 / 471722798391) := by
    rw [show ((471722798391 / 125000000000) : ℝ) = ((125000000000 / 471722798391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (667762299 / 500000000) ≤ -Real.log (500000000000 / 1900994972317) ∧
    -Real.log (500000000000 / 1900994972317) ≤ (6677623 / 5000000) := by
  have h := checkLog_sound (w := (900994972317 / 2900994972317)) (n := 12)
    (lo := (321188709 / 500000000)) (hi := (642377419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1900994972317 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1900994972317 / 1000000000000) = 1/(500000000000 / 1900994972317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (667762299 / 500000000) (6677623 / 5000000) (Real.log (1900994972317 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1900994972317 / 500000000000) = -Real.log (500000000000 / 1900994972317) := by
    rw [show ((1900994972317 / 500000000000) : ℝ) = ((500000000000 / 1900994972317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0036

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0037Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0037
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

theorem reflection_log_1_neg : (24058967 / 62500000) ≤ -Real.log (1280 / 1881) ∧
    -Real.log (1280 / 1881) ≤ (384943473 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 3161)) (n := 12)
    (lo := (24058967 / 62500000)) (hi := (384943473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881 / 1280) = 1/(1280 / 1881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24058967 / 62500000) (384943473 / 1000000000) (Real.log (1881 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1881 / 1280) = -Real.log (1280 / 1881) := by
    rw [show ((1881 / 1280) : ℝ) = ((1280 / 1881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (633994229 / 1000000000) ≤ -Real.log (679 / 1280) ∧
    -Real.log (679 / 1280) ≤ (63399423 / 100000000) := by
  have h := checkLog_sound (w := (601 / 1959)) (n := 12)
    (lo := (633994229 / 1000000000)) (hi := (63399423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 679) = 1/(679 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63399423 / 100000000) (-633994229 / 1000000000) (Real.log (679 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (192072853 / 500000000) ≤ -Real.log (2560 / 3759) ∧
    -Real.log (2560 / 3759) ≤ (384145707 / 1000000000) := by
  have h := checkLog_sound (w := (1199 / 6319)) (n := 12)
    (lo := (192072853 / 500000000)) (hi := (384145707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3759 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3759 / 2560) = 1/(2560 / 3759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (192072853 / 500000000) (384145707 / 1000000000) (Real.log (3759 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3759 / 2560) = -Real.log (2560 / 3759) := by
    rw [show ((3759 / 2560) : ℝ) = ((2560 / 3759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (315893767 / 500000000) ≤ -Real.log (1361 / 2560) ∧
    -Real.log (1361 / 2560) ≤ (126357507 / 200000000) := by
  have h := checkLog_sound (w := (1199 / 3921)) (n := 12)
    (lo := (315893767 / 500000000)) (hi := (126357507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1361) = 1/(1361 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-126357507 / 200000000) (-315893767 / 500000000) (Real.log (1361 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10346947 / 15625000) ≤ -Real.log (640 / 1241) ∧
    -Real.log (640 / 1241) ≤ (662204609 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 1881)) (n := 12)
    (lo := (10346947 / 15625000)) (hi := (662204609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241 / 640) = 1/(640 / 1241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10346947 / 15625000) (662204609 / 1000000000) (Real.log (1241 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1241 / 640) = -Real.log (640 / 1241) := by
    rw [show ((1241 / 640) : ℝ) = ((640 / 1241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2797906527 / 1000000000) ≤ -Real.log (39 / 640) ∧
    -Real.log (39 / 640) ≤ (699476633 / 250000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 39) = 1/(39 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-699476633 / 250000000) (-2797906527 / 1000000000) (Real.log (39 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (26439807 / 40000000) ≤ -Real.log (1280 / 2479) ∧
    -Real.log (1280 / 2479) ≤ (82624397 / 125000000) := by
  have h := checkLog_sound (w := (1199 / 3759)) (n := 12)
    (lo := (26439807 / 40000000)) (hi := (82624397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2479 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2479 / 1280) = 1/(1280 / 2479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (26439807 / 40000000) (82624397 / 125000000) (Real.log (2479 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2479 / 1280) = -Real.log (1280 / 2479) := by
    rw [show ((2479 / 1280) : ℝ) = ((1280 / 2479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (13800831 / 5000000) ≤ -Real.log (81 / 1280) ∧
    -Real.log (81 / 1280) ≤ (690041551 / 250000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 81) = 1/(81 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-690041551 / 250000000) (-13800831 / 5000000) (Real.log (81 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (534614999 / 1000000000) ≤ -Real.log (1000000 / 1706791) ∧
    -Real.log (1000000 / 1706791) ≤ (106923 / 200000) := by
  have h := checkLog_sound (w := (706791 / 2706791)) (n := 12)
    (lo := (534614999 / 1000000000)) (hi := (106923 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1706791 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1706791 / 1000000) = 1/(1000000 / 1706791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (534614999 / 1000000000) (106923 / 200000) (Real.log (1706791 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1706791 / 1000000) = -Real.log (1000000 / 1706791) := by
    rw [show ((1706791 / 1000000) : ℝ) = ((1000000 / 1706791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1226869613 / 1000000000) ≤ -Real.log (293209 / 1000000) ∧
    -Real.log (293209 / 1000000) ≤ (245373923 / 200000000) := by
  have h := checkLog_sound (w := (206791 / 793209)) (n := 12)
    (lo := (533722433 / 1000000000)) (hi := (266861217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 293209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 293209) = 1/(293209 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-245373923 / 200000000) (-1226869613 / 1000000000) (Real.log (293209 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16748509 / 31250000) ≤ -Real.log (40000 / 68363) ∧
    -Real.log (40000 / 68363) ≤ (535952289 / 1000000000) := by
  have h := checkLog_sound (w := (28363 / 108363)) (n := 12)
    (lo := (16748509 / 31250000)) (hi := (535952289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68363 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68363 / 40000) = 1/(40000 / 68363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16748509 / 31250000) (535952289 / 1000000000) (Real.log (68363 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (68363 / 40000) = -Real.log (40000 / 68363) := by
    rw [show ((68363 / 40000) : ℝ) = ((40000 / 68363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (77168111 / 62500000) ≤ -Real.log (11637 / 40000) ∧
    -Real.log (11637 / 40000) ≤ (617344889 / 500000000) := by
  have h := checkLog_sound (w := (8363 / 31637)) (n := 12)
    (lo := (135385649 / 250000000)) (hi := (541542597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11637) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 11637) = 1/(11637 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-617344889 / 500000000) (-77168111 / 62500000) (Real.log (11637 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (456542179 / 1000000000) ≤ -Real.log (500000 / 789303) ∧
    -Real.log (500000 / 789303) ≤ (22827109 / 50000000) := by
  have h := checkLog_sound (w := (289303 / 1289303)) (n := 12)
    (lo := (456542179 / 1000000000)) (hi := (22827109 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789303 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789303 / 500000) = 1/(500000 / 789303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (456542179 / 1000000000) (22827109 / 50000000) (Real.log (789303 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (789303 / 500000) = -Real.log (500000 / 789303) := by
    rw [show ((789303 / 500000) : ℝ) = ((500000 / 789303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172837403 / 200000000) ≤ -Real.log (210697 / 500000) ∧
    -Real.log (210697 / 500000) ≤ (864187017 / 1000000000) := by
  have h := checkLog_sound (w := (39303 / 460697)) (n := 12)
    (lo := (34207967 / 200000000)) (hi := (42759959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210697) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 210697) = 1/(210697 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-864187017 / 1000000000) (-172837403 / 200000000) (Real.log (210697 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (458086653 / 1000000000) ≤ -Real.log (500000 / 790523) ∧
    -Real.log (500000 / 790523) ≤ (229043327 / 500000000) := by
  have h := checkLog_sound (w := (290523 / 1290523)) (n := 12)
    (lo := (458086653 / 1000000000)) (hi := (229043327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790523 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790523 / 500000) = 1/(500000 / 790523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (458086653 / 1000000000) (229043327 / 500000000) (Real.log (790523 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (790523 / 500000) = -Real.log (500000 / 790523) := by
    rw [show ((790523 / 500000) : ℝ) = ((500000 / 790523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (869994149 / 1000000000) ≤ -Real.log (209477 / 500000) ∧
    -Real.log (209477 / 500000) ≤ (869994151 / 1000000000) := by
  have h := checkLog_sound (w := (40523 / 459477)) (n := 12)
    (lo := (176846969 / 1000000000)) (hi := (17684697 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 209477) = 1/(209477 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-869994151 / 1000000000) (-869994149 / 1000000000) (Real.log (209477 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1761484611 / 1000000000) ≤ -Real.log (250000000000 / 1455268255749) ∧
    -Real.log (250000000000 / 1455268255749) ≤ (880742307 / 500000000) := by
  have h := checkLog_sound (w := (455268255749 / 2455268255749)) (n := 12)
    (lo := (375190251 / 1000000000)) (hi := (93797563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455268255749 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1455268255749 / 1000000000000) = 1/(250000000000 / 1455268255749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1761484611 / 1000000000) (880742307 / 500000000) (Real.log (1455268255749 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1455268255749 / 250000000000) = -Real.log (250000000000 / 1455268255749) := by
    rw [show ((1455268255749 / 250000000000) : ℝ) = ((250000000000 / 1455268255749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (110665129 / 62500000) ≤ -Real.log (500000000000 / 2937312021999) ∧
    -Real.log (500000000000 / 2937312021999) ≤ (1770642067 / 1000000000) := by
  have h := checkLog_sound (w := (937312021999 / 4937312021999)) (n := 12)
    (lo := (48043463 / 125000000)) (hi := (76869541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2937312021999 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2937312021999 / 2000000000000) = 1/(500000000000 / 2937312021999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (110665129 / 62500000) (1770642067 / 1000000000) (Real.log (2937312021999 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2937312021999 / 500000000000) = -Real.log (500000000000 / 2937312021999) := by
    rw [show ((2937312021999 / 500000000000) : ℝ) = ((500000000000 / 2937312021999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (660364597 / 500000000) ≤ -Real.log (500000000000 / 1873076028609) ∧
    -Real.log (500000000000 / 1873076028609) ≤ (330182299 / 250000000) := by
  have h := checkLog_sound (w := (873076028609 / 2873076028609)) (n := 12)
    (lo := (313791007 / 500000000)) (hi := (125516403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1873076028609 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1873076028609 / 1000000000000) = 1/(500000000000 / 1873076028609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (660364597 / 500000000) (330182299 / 250000000) (Real.log (1873076028609 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1873076028609 / 500000000000) = -Real.log (500000000000 / 1873076028609) := by
    rw [show ((1873076028609 / 500000000000) : ℝ) = ((500000000000 / 1873076028609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1328080803 / 1000000000) ≤ -Real.log (500000000000 / 1886896890829) ∧
    -Real.log (500000000000 / 1886896890829) ≤ (265616161 / 200000000) := by
  have h := checkLog_sound (w := (886896890829 / 2886896890829)) (n := 12)
    (lo := (634933623 / 1000000000)) (hi := (79366703 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886896890829 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1886896890829 / 1000000000000) = 1/(500000000000 / 1886896890829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1328080803 / 1000000000) (265616161 / 200000000) (Real.log (1886896890829 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1886896890829 / 500000000000) = -Real.log (500000000000 / 1886896890829) := by
    rw [show ((1886896890829 / 500000000000) : ℝ) = ((500000000000 / 1886896890829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0037

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0038Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0038
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

theorem reflection_log_1_neg : (192072853 / 500000000) ≤ -Real.log (2560 / 3759) ∧
    -Real.log (2560 / 3759) ≤ (384145707 / 1000000000) := by
  have h := checkLog_sound (w := (1199 / 6319)) (n := 12)
    (lo := (192072853 / 500000000)) (hi := (384145707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3759 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3759 / 2560) = 1/(2560 / 3759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (192072853 / 500000000) (384145707 / 1000000000) (Real.log (3759 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3759 / 2560) = -Real.log (2560 / 3759) := by
    rw [show ((3759 / 2560) : ℝ) = ((2560 / 3759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (315893767 / 500000000) ≤ -Real.log (1361 / 2560) ∧
    -Real.log (1361 / 2560) ≤ (126357507 / 200000000) := by
  have h := checkLog_sound (w := (1199 / 3921)) (n := 12)
    (lo := (315893767 / 500000000)) (hi := (126357507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1361) = 1/(1361 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-126357507 / 200000000) (-315893767 / 500000000) (Real.log (1361 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (191673651 / 500000000) ≤ -Real.log (640 / 939) ∧
    -Real.log (640 / 939) ≤ (383347303 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1579)) (n := 12)
    (lo := (191673651 / 500000000)) (hi := (383347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939 / 640) = 1/(640 / 939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (191673651 / 500000000) (383347303 / 1000000000) (Real.log (939 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (939 / 640) = -Real.log (640 / 939) := by
    rw [show ((939 / 640) : ℝ) = ((640 / 939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (629585699 / 1000000000) ≤ -Real.log (341 / 640) ∧
    -Real.log (341 / 640) ≤ (6295857 / 10000000) := by
  have h := checkLog_sound (w := (299 / 981)) (n := 12)
    (lo := (629585699 / 1000000000)) (hi := (6295857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 341) = 1/(341 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6295857 / 10000000) (-629585699 / 1000000000) (Real.log (341 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (26439807 / 40000000) ≤ -Real.log (1280 / 2479) ∧
    -Real.log (1280 / 2479) ≤ (82624397 / 125000000) := by
  have h := checkLog_sound (w := (1199 / 3759)) (n := 12)
    (lo := (26439807 / 40000000)) (hi := (82624397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2479 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2479 / 1280) = 1/(1280 / 2479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (26439807 / 40000000) (82624397 / 125000000) (Real.log (2479 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2479 / 1280) = -Real.log (1280 / 2479) := by
    rw [show ((2479 / 1280) : ℝ) = ((1280 / 2479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (13800831 / 5000000) ≤ -Real.log (81 / 1280) ∧
    -Real.log (81 / 1280) ≤ (690041551 / 250000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 81) = 1/(81 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-690041551 / 250000000) (-13800831 / 5000000) (Real.log (81 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (164946069 / 250000000) ≤ -Real.log (320 / 619) ∧
    -Real.log (320 / 619) ≤ (659784277 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 939)) (n := 12)
    (lo := (164946069 / 250000000)) (hi := (659784277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619 / 320) = 1/(320 / 619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (164946069 / 250000000) (659784277 / 1000000000) (Real.log (619 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619 / 320) = -Real.log (320 / 619) := by
    rw [show ((619 / 320) : ℝ) = ((320 / 619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (680949639 / 250000000) ≤ -Real.log (21 / 320) ∧
    -Real.log (21 / 320) ≤ (17023741 / 6250000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 21) = 1/(21 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-17023741 / 6250000) (-680949639 / 250000000) (Real.log (21 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (533284719 / 1000000000) ≤ -Real.log (500000 / 852261) ∧
    -Real.log (500000 / 852261) ≤ (6666059 / 12500000) := by
  have h := checkLog_sound (w := (352261 / 1352261)) (n := 12)
    (lo := (533284719 / 1000000000)) (hi := (6666059 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852261 / 500000) = 1/(500000 / 852261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (533284719 / 1000000000) (6666059 / 12500000) (Real.log (852261 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (852261 / 500000) = -Real.log (500000 / 852261) := by
    rw [show ((852261 / 500000) : ℝ) = ((500000 / 852261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (609580447 / 500000000) ≤ -Real.log (147739 / 500000) ∧
    -Real.log (147739 / 500000) ≤ (19049389 / 15625000) := by
  have h := checkLog_sound (w := (102261 / 397739)) (n := 12)
    (lo := (263006857 / 500000000)) (hi := (105202743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 147739) = 1/(147739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19049389 / 15625000) (-609580447 / 500000000) (Real.log (147739 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (106923117 / 200000000) ≤ -Real.log (125000 / 213349) ∧
    -Real.log (125000 / 213349) ≤ (267307793 / 500000000) := by
  have h := checkLog_sound (w := (88349 / 338349)) (n := 12)
    (lo := (106923117 / 200000000)) (hi := (267307793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213349 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213349 / 125000) = 1/(125000 / 213349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (106923117 / 200000000) (267307793 / 500000000) (Real.log (213349 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (213349 / 125000) = -Real.log (125000 / 213349) := by
    rw [show ((213349 / 125000) : ℝ) = ((125000 / 213349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1226873023 / 1000000000) ≤ -Real.log (36651 / 125000) ∧
    -Real.log (36651 / 125000) ≤ (49074921 / 40000000) := by
  have h := checkLog_sound (w := (25849 / 99151)) (n := 12)
    (lo := (533725843 / 1000000000)) (hi := (133431461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36651) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 36651) = 1/(36651 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49074921 / 40000000) (-1226873023 / 1000000000) (Real.log (36651 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (455009273 / 1000000000) ≤ -Real.log (250000 / 394047) ∧
    -Real.log (250000 / 394047) ≤ (227504637 / 500000000) := by
  have h := checkLog_sound (w := (144047 / 644047)) (n := 12)
    (lo := (455009273 / 1000000000)) (hi := (227504637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394047 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394047 / 250000) = 1/(250000 / 394047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (455009273 / 1000000000) (227504637 / 500000000) (Real.log (394047 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (394047 / 250000) = -Real.log (250000 / 394047) := by
    rw [show ((394047 / 250000) : ℝ) = ((250000 / 394047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (858465317 / 1000000000) ≤ -Real.log (105953 / 250000) ∧
    -Real.log (105953 / 250000) ≤ (858465319 / 1000000000) := by
  have h := checkLog_sound (w := (19047 / 230953)) (n := 12)
    (lo := (165318137 / 1000000000)) (hi := (82659069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105953) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 105953) = 1/(105953 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-858465319 / 1000000000) (-858465317 / 1000000000) (Real.log (105953 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (114135703 / 250000000) ≤ -Real.log (1000000 / 1578607) ∧
    -Real.log (1000000 / 1578607) ≤ (456542813 / 1000000000) := by
  have h := checkLog_sound (w := (578607 / 2578607)) (n := 12)
    (lo := (114135703 / 250000000)) (hi := (456542813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1578607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1578607 / 1000000) = 1/(1000000 / 1578607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114135703 / 250000000) (456542813 / 1000000000) (Real.log (1578607 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1578607 / 1000000) = -Real.log (1000000 / 1578607) := by
    rw [show ((1578607 / 1000000) : ℝ) = ((1000000 / 1578607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (216047347 / 250000000) ≤ -Real.log (421393 / 1000000) ∧
    -Real.log (421393 / 1000000) ≤ (86418939 / 100000000) := by
  have h := checkLog_sound (w := (78607 / 921393)) (n := 12)
    (lo := (5345069 / 31250000)) (hi := (171042209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 421393) = 1/(421393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-86418939 / 100000000) (-216047347 / 250000000) (Real.log (421393 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1752445613 / 1000000000) ≤ -Real.log (7812500000 / 45067917493) ∧
    -Real.log (7812500000 / 45067917493) ≤ (109527851 / 62500000) := by
  have h := checkLog_sound (w := (13817917493 / 76317917493)) (n := 12)
    (lo := (366151253 / 1000000000)) (hi := (183075627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45067917493 / 31250000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(45067917493 / 31250000000) = 1/(7812500000 / 45067917493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1752445613 / 1000000000) (109527851 / 62500000) (Real.log (45067917493 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45067917493 / 7812500000) = -Real.log (7812500000 / 45067917493) := by
    rw [show ((45067917493 / 7812500000) : ℝ) = ((7812500000 / 45067917493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (55046519 / 31250000) ≤ -Real.log (250000000000 / 1455274071649) ∧
    -Real.log (250000000000 / 1455274071649) ≤ (1761488611 / 1000000000) := by
  have h := checkLog_sound (w := (455274071649 / 2455274071649)) (n := 12)
    (lo := (46899281 / 125000000)) (hi := (375194249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455274071649 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1455274071649 / 1000000000000) = 1/(250000000000 / 1455274071649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (55046519 / 31250000) (1761488611 / 1000000000) (Real.log (1455274071649 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1455274071649 / 250000000000) = -Real.log (250000000000 / 1455274071649) := by
    rw [show ((1455274071649 / 250000000000) : ℝ) = ((250000000000 / 1455274071649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1313474591 / 1000000000) ≤ -Real.log (25000000000 / 92976838787) ∧
    -Real.log (25000000000 / 92976838787) ≤ (1313474593 / 1000000000) := by
  have h := checkLog_sound (w := (42976838787 / 142976838787)) (n := 12)
    (lo := (620327411 / 1000000000)) (hi := (155081853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92976838787 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(92976838787 / 50000000000) = 1/(25000000000 / 92976838787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1313474591 / 1000000000) (1313474593 / 1000000000) (Real.log (92976838787 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (92976838787 / 25000000000) = -Real.log (25000000000 / 92976838787) := by
    rw [show ((92976838787 / 25000000000) : ℝ) = ((25000000000 / 92976838787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1320732201 / 1000000000) ≤ -Real.log (250000000000 / 936540830057) ∧
    -Real.log (250000000000 / 936540830057) ≤ (1320732203 / 1000000000) := by
  have h := checkLog_sound (w := (436540830057 / 1436540830057)) (n := 12)
    (lo := (627585021 / 1000000000)) (hi := (313792511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((936540830057 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(936540830057 / 500000000000) = 1/(250000000000 / 936540830057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1320732201 / 1000000000) (1320732203 / 1000000000) (Real.log (936540830057 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (936540830057 / 250000000000) = -Real.log (250000000000 / 936540830057) := by
    rw [show ((936540830057 / 250000000000) : ℝ) = ((250000000000 / 936540830057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0038

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0039Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0039
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

theorem reflection_log_1_neg : (191673651 / 500000000) ≤ -Real.log (640 / 939) ∧
    -Real.log (640 / 939) ≤ (383347303 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1579)) (n := 12)
    (lo := (191673651 / 500000000)) (hi := (383347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939 / 640) = 1/(640 / 939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (191673651 / 500000000) (383347303 / 1000000000) (Real.log (939 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (939 / 640) = -Real.log (640 / 939) := by
    rw [show ((939 / 640) : ℝ) = ((640 / 939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (629585699 / 1000000000) ≤ -Real.log (341 / 640) ∧
    -Real.log (341 / 640) ≤ (6295857 / 10000000) := by
  have h := checkLog_sound (w := (299 / 981)) (n := 12)
    (lo := (629585699 / 1000000000)) (hi := (6295857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 341) = 1/(341 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6295857 / 10000000) (-629585699 / 1000000000) (Real.log (341 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (382548261 / 1000000000) ≤ -Real.log (2560 / 3753) ∧
    -Real.log (2560 / 3753) ≤ (191274131 / 500000000) := by
  have h := checkLog_sound (w := (1193 / 6313)) (n := 12)
    (lo := (382548261 / 1000000000)) (hi := (191274131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3753 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3753 / 2560) = 1/(2560 / 3753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (382548261 / 1000000000) (191274131 / 500000000) (Real.log (3753 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3753 / 2560) = -Real.log (2560 / 3753) := by
    rw [show ((3753 / 2560) : ℝ) = ((2560 / 3753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6273887 / 10000000) ≤ -Real.log (1367 / 2560) ∧
    -Real.log (1367 / 2560) ≤ (627388701 / 1000000000) := by
  have h := checkLog_sound (w := (1193 / 3927)) (n := 12)
    (lo := (6273887 / 10000000)) (hi := (627388701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1367) = 1/(1367 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-627388701 / 1000000000) (-6273887 / 10000000) (Real.log (1367 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (164946069 / 250000000) ≤ -Real.log (320 / 619) ∧
    -Real.log (320 / 619) ≤ (659784277 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 939)) (n := 12)
    (lo := (164946069 / 250000000)) (hi := (659784277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619 / 320) = 1/(320 / 619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (164946069 / 250000000) (659784277 / 1000000000) (Real.log (619 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (619 / 320) = -Real.log (320 / 619) := by
    rw [show ((619 / 320) : ℝ) = ((320 / 619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (680949639 / 250000000) ≤ -Real.log (21 / 320) ∧
    -Real.log (21 / 320) ≤ (17023741 / 6250000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 21) = 1/(21 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-17023741 / 6250000) (-680949639 / 250000000) (Real.log (21 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (65857191 / 100000000) ≤ -Real.log (1280 / 2473) ∧
    -Real.log (1280 / 2473) ≤ (658571911 / 1000000000) := by
  have h := checkLog_sound (w := (1193 / 3753)) (n := 12)
    (lo := (65857191 / 100000000)) (hi := (658571911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2473 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2473 / 1280) = 1/(1280 / 2473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (65857191 / 100000000) (658571911 / 1000000000) (Real.log (2473 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2473 / 1280) = -Real.log (1280 / 2473) := by
    rw [show ((2473 / 1280) : ℝ) = ((1280 / 2473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (672176809 / 250000000) ≤ -Real.log (87 / 1280) ∧
    -Real.log (87 / 1280) ≤ (67217681 / 25000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 87) = 1/(87 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-67217681 / 25000000) (-672176809 / 250000000) (Real.log (87 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (531959717 / 1000000000) ≤ -Real.log (200000 / 340453) ∧
    -Real.log (200000 / 340453) ≤ (265979859 / 500000000) := by
  have h := checkLog_sound (w := (140453 / 540453)) (n := 12)
    (lo := (531959717 / 1000000000)) (hi := (265979859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340453 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340453 / 200000) = 1/(200000 / 340453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (531959717 / 1000000000) (265979859 / 500000000) (Real.log (340453 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (340453 / 200000) = -Real.log (200000 / 340453) := by
    rw [show ((340453 / 200000) : ℝ) = ((200000 / 340453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1211551449 / 1000000000) ≤ -Real.log (59547 / 200000) ∧
    -Real.log (59547 / 200000) ≤ (1211551451 / 1000000000) := by
  have h := checkLog_sound (w := (40453 / 159547)) (n := 12)
    (lo := (518404269 / 1000000000)) (hi := (51840427 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 59547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 59547) = 1/(59547 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1211551451 / 1000000000) (-1211551449 / 1000000000) (Real.log (59547 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266642653 / 500000000) ≤ -Real.log (1000000 / 1704523) ∧
    -Real.log (1000000 / 1704523) ≤ (533285307 / 1000000000) := by
  have h := checkLog_sound (w := (704523 / 2704523)) (n := 12)
    (lo := (266642653 / 500000000)) (hi := (533285307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1704523 / 1000000) = 1/(1000000 / 1704523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266642653 / 500000000) (533285307 / 1000000000) (Real.log (1704523 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1704523 / 1000000) = -Real.log (1000000 / 1704523) := by
    rw [show ((1704523 / 1000000) : ℝ) = ((1000000 / 1704523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (609582139 / 500000000) ≤ -Real.log (295477 / 1000000) ∧
    -Real.log (295477 / 1000000) ≤ (30479107 / 25000000) := by
  have h := checkLog_sound (w := (204523 / 795477)) (n := 12)
    (lo := (263008549 / 500000000)) (hi := (526017099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 295477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 295477) = 1/(295477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-30479107 / 25000000) (-609582139 / 500000000) (Real.log (295477 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (453486087 / 1000000000) ≤ -Real.log (1000000 / 1573789) ∧
    -Real.log (1000000 / 1573789) ≤ (56685761 / 125000000) := by
  have h := checkLog_sound (w := (573789 / 2573789)) (n := 12)
    (lo := (453486087 / 1000000000)) (hi := (56685761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1573789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1573789 / 1000000) = 1/(1000000 / 1573789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (453486087 / 1000000000) (56685761 / 125000000) (Real.log (1573789 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1573789 / 1000000) = -Real.log (1000000 / 1573789) := by
    rw [show ((1573789 / 1000000) : ℝ) = ((1000000 / 1573789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (852820749 / 1000000000) ≤ -Real.log (426211 / 1000000) ∧
    -Real.log (426211 / 1000000) ≤ (852820751 / 1000000000) := by
  have h := checkLog_sound (w := (73789 / 926211)) (n := 12)
    (lo := (159673569 / 1000000000)) (hi := (15967357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 426211) = 1/(426211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-852820751 / 1000000000) (-852820749 / 1000000000) (Real.log (426211 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (113752477 / 250000000) ≤ -Real.log (1000000 / 1576189) ∧
    -Real.log (1000000 / 1576189) ≤ (455009909 / 1000000000) := by
  have h := checkLog_sound (w := (576189 / 2576189)) (n := 12)
    (lo := (113752477 / 250000000)) (hi := (455009909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1576189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1576189 / 1000000) = 1/(1000000 / 1576189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (113752477 / 250000000) (455009909 / 1000000000) (Real.log (1576189 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1576189 / 1000000) = -Real.log (1000000 / 1576189) := by
    rw [show ((1576189 / 1000000) : ℝ) = ((1000000 / 1576189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (858467677 / 1000000000) ≤ -Real.log (423811 / 1000000) ∧
    -Real.log (423811 / 1000000) ≤ (858467679 / 1000000000) := by
  have h := checkLog_sound (w := (76189 / 923811)) (n := 12)
    (lo := (165320497 / 1000000000)) (hi := (82660249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423811) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 423811) = 1/(423811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-858467679 / 1000000000) (-858467677 / 1000000000) (Real.log (423811 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (348702233 / 200000000) ≤ -Real.log (500000000000 / 2858691453809) ∧
    -Real.log (500000000000 / 2858691453809) ≤ (13621181 / 7812500) := by
  have h := checkLog_sound (w := (858691453809 / 4858691453809)) (n := 12)
    (lo := (71443361 / 200000000)) (hi := (178608403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2858691453809 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2858691453809 / 2000000000000) = 1/(500000000000 / 2858691453809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (348702233 / 200000000) (13621181 / 7812500) (Real.log (2858691453809 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2858691453809 / 500000000000) = -Real.log (500000000000 / 2858691453809) := by
    rw [show ((2858691453809 / 500000000000) : ℝ) = ((500000000000 / 2858691453809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (109528099 / 62500000) ≤ -Real.log (100000000000 / 576871634679) ∧
    -Real.log (100000000000 / 576871634679) ≤ (1752449587 / 1000000000) := by
  have h := checkLog_sound (w := (176871634679 / 976871634679)) (n := 12)
    (lo := (45769403 / 125000000)) (hi := (14646209 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576871634679 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(576871634679 / 400000000000) = 1/(100000000000 / 576871634679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (109528099 / 62500000) (1752449587 / 1000000000) (Real.log (576871634679 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (576871634679 / 100000000000) = -Real.log (100000000000 / 576871634679) := by
    rw [show ((576871634679 / 100000000000) : ℝ) = ((100000000000 / 576871634679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1306306837 / 1000000000) ≤ -Real.log (125000000000 / 461563931949) ∧
    -Real.log (125000000000 / 461563931949) ≤ (1306306839 / 1000000000) := by
  have h := checkLog_sound (w := (211563931949 / 711563931949)) (n := 12)
    (lo := (613159657 / 1000000000)) (hi := (306579829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461563931949 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(461563931949 / 250000000000) = 1/(125000000000 / 461563931949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1306306837 / 1000000000) (1306306839 / 1000000000) (Real.log (461563931949 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (461563931949 / 125000000000) = -Real.log (125000000000 / 461563931949) := by
    rw [show ((461563931949 / 125000000000) : ℝ) = ((125000000000 / 461563931949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (262695517 / 200000000) ≤ -Real.log (976562500 / 3631918639) ∧
    -Real.log (976562500 / 3631918639) ≤ (1313477587 / 1000000000) := by
  have h := checkLog_sound (w := (1678793639 / 5585043639)) (n := 12)
    (lo := (124066081 / 200000000)) (hi := (310165203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3631918639 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3631918639 / 1953125000) = 1/(976562500 / 3631918639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (262695517 / 200000000) (1313477587 / 1000000000) (Real.log (3631918639 / 976562500)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3631918639 / 976562500) = -Real.log (976562500 / 3631918639) := by
    rw [show ((3631918639 / 976562500) : ℝ) = ((976562500 / 3631918639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0039

end


