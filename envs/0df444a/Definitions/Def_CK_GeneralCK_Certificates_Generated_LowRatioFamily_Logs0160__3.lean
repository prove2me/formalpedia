-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T04:55:46.8082+00:00
-- url     : https://prove2.me/theorems/69a0dee5-0e6d-432f-a50b-56f08a42c85c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0160 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0161, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0162).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10368_neg : (344059 / 1000000000) ≤ -Real.log (124957 / 125000) ∧
    -Real.log (124957 / 125000) ≤ (17203 / 50000000) := by
  have h := checkLog_sound (w := (43 / 249957)) (n := 12)
    (lo := (344059 / 1000000000)) (hi := (17203 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124957) = 1/(124957 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10368 : Bounds (-17203 / 50000000) (-344059 / 1000000000) (Real.log (124957 / 125000)) := by
  have h := reflection_log_10368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10369_neg : (20169369 / 125000000) ≤ -Real.log (500000 / 587551) ∧
    -Real.log (500000 / 587551) ≤ (161354953 / 1000000000) := by
  have h := checkLog_sound (w := (87551 / 1087551)) (n := 12)
    (lo := (20169369 / 125000000)) (hi := (161354953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587551 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587551 / 500000) = 1/(500000 / 587551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10369 : Bounds (20169369 / 125000000) (161354953 / 1000000000) (Real.log (587551 / 500000)) := by
  have h := reflection_log_10369_neg
  have he : Real.log (587551 / 500000) = -Real.log (500000 / 587551) := by
    rw [show ((587551 / 500000) : ℝ) = ((500000 / 587551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10370_neg : (12030971 / 62500000) ≤ -Real.log (412449 / 500000) ∧
    -Real.log (412449 / 500000) ≤ (192495537 / 1000000000) := by
  have h := checkLog_sound (w := (87551 / 912449)) (n := 12)
    (lo := (12030971 / 62500000)) (hi := (192495537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 412449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 412449) = 1/(412449 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10370 : Bounds (-192495537 / 1000000000) (-12030971 / 62500000) (Real.log (412449 / 500000)) := by
  have h := reflection_log_10370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10371_neg : (16209589 / 100000000) ≤ -Real.log (1000000 / 1175973) ∧
    -Real.log (1000000 / 1175973) ≤ (162095891 / 1000000000) := by
  have h := checkLog_sound (w := (175973 / 2175973)) (n := 12)
    (lo := (16209589 / 100000000)) (hi := (162095891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1175973 / 1000000) = 1/(1000000 / 1175973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10371 : Bounds (16209589 / 100000000) (162095891 / 1000000000) (Real.log (1175973 / 1000000)) := by
  have h := reflection_log_10371_neg
  have he : Real.log (1175973 / 1000000) = -Real.log (1000000 / 1175973) := by
    rw [show ((1175973 / 1000000) : ℝ) = ((1000000 / 1175973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10372_neg : (96775991 / 500000000) ≤ -Real.log (824027 / 1000000) ∧
    -Real.log (824027 / 1000000) ≤ (193551983 / 1000000000) := by
  have h := checkLog_sound (w := (175973 / 1824027)) (n := 12)
    (lo := (96775991 / 500000000)) (hi := (193551983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 824027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 824027) = 1/(824027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10372 : Bounds (-193551983 / 1000000000) (-96775991 / 500000000) (Real.log (824027 / 1000000)) := by
  have h := reflection_log_10372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10373_neg : (7864023 / 250000000) ≤ -Real.log (969033503271 / 1000000000000) ∧
    -Real.log (969033503271 / 1000000000000) ≤ (31456093 / 1000000000) := by
  have h := checkLog_sound (w := (30966496729 / 1969033503271)) (n := 12)
    (lo := (7864023 / 250000000)) (hi := (31456093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969033503271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969033503271) = 1/(969033503271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10373 : Bounds (-31456093 / 1000000000) (-7864023 / 250000000) (Real.log (969033503271 / 1000000000000)) := by
  have h := reflection_log_10373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10374_neg : (3892573 / 125000000) ≤ -Real.log (242334822399 / 250000000000) ∧
    -Real.log (242334822399 / 250000000000) ≤ (6228117 / 200000000) := by
  have h := checkLog_sound (w := (7665177601 / 492334822399)) (n := 12)
    (lo := (3892573 / 125000000)) (hi := (6228117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242334822399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242334822399) = 1/(242334822399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10374 : Bounds (-6228117 / 200000000) (-3892573 / 125000000) (Real.log (242334822399 / 250000000000)) := by
  have h := reflection_log_10374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10375_neg : (44231311 / 125000000) ≤ -Real.log (50000000000 / 71227109291) ∧
    -Real.log (50000000000 / 71227109291) ≤ (353850489 / 1000000000) := by
  have h := checkLog_sound (w := (21227109291 / 121227109291)) (n := 12)
    (lo := (44231311 / 125000000)) (hi := (353850489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71227109291 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71227109291 / 50000000000) = 1/(50000000000 / 71227109291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10375 : Bounds (44231311 / 125000000) (353850489 / 1000000000) (Real.log (71227109291 / 50000000000)) := by
  have h := reflection_log_10375_neg
  have he : Real.log (71227109291 / 50000000000) = -Real.log (50000000000 / 71227109291) := by
    rw [show ((71227109291 / 50000000000) : ℝ) = ((50000000000 / 71227109291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10376_neg : (2778499 / 7812500) ≤ -Real.log (125000000000 / 178388117137) ∧
    -Real.log (125000000000 / 178388117137) ≤ (355647873 / 1000000000) := by
  have h := checkLog_sound (w := (53388117137 / 303388117137)) (n := 12)
    (lo := (2778499 / 7812500)) (hi := (355647873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178388117137 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178388117137 / 125000000000) = 1/(125000000000 / 178388117137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10376 : Bounds (2778499 / 7812500) (355647873 / 1000000000) (Real.log (178388117137 / 125000000000)) := by
  have h := reflection_log_10376_neg
  have he : Real.log (178388117137 / 125000000000) = -Real.log (125000000000 / 178388117137) := by
    rw [show ((178388117137 / 125000000000) : ℝ) = ((125000000000 / 178388117137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10377_neg : (714977177 / 1000000000) ≤ -Real.log (25000000000 / 51103500761) ∧
    -Real.log (25000000000 / 51103500761) ≤ (714977179 / 1000000000) := by
  have h := checkLog_sound (w := (1103500761 / 101103500761)) (n := 12)
    (lo := (21829997 / 1000000000)) (hi := (10914999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51103500761 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51103500761 / 50000000000) = 1/(25000000000 / 51103500761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10377 : Bounds (714977177 / 1000000000) (714977179 / 1000000000) (Real.log (51103500761 / 25000000000)) := by
  have h := reflection_log_10377_neg
  have he : Real.log (51103500761 / 25000000000) = -Real.log (25000000000 / 51103500761) := by
    rw [show ((51103500761 / 25000000000) : ℝ) = ((25000000000 / 51103500761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10378_neg : (717244731 / 1000000000) ≤ -Real.log (500000000000 / 1024390243903) ∧
    -Real.log (500000000000 / 1024390243903) ≤ (717244733 / 1000000000) := by
  have h := checkLog_sound (w := (24390243903 / 2024390243903)) (n := 12)
    (lo := (24097551 / 1000000000)) (hi := (1506097 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024390243903 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1024390243903 / 1000000000000) = 1/(500000000000 / 1024390243903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10378 : Bounds (717244731 / 1000000000) (717244733 / 1000000000) (Real.log (1024390243903 / 500000000000)) := by
  have h := reflection_log_10378_neg
  have he : Real.log (1024390243903 / 500000000000) = -Real.log (500000000000 / 1024390243903) := by
    rw [show ((1024390243903 / 500000000000) : ℝ) = ((500000000000 / 1024390243903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10379_neg : (296394013 / 1000000000) ≤ -Real.log (200 / 269) ∧
    -Real.log (200 / 269) ≤ (148197007 / 500000000) := by
  have h := checkLog_sound (w := (69 / 469)) (n := 12)
    (lo := (296394013 / 1000000000)) (hi := (148197007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269 / 200) = 1/(200 / 269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10379 : Bounds (296394013 / 1000000000) (148197007 / 500000000) (Real.log (269 / 200)) := by
  have h := reflection_log_10379_neg
  have he : Real.log (269 / 200) = -Real.log (200 / 269) := by
    rw [show ((269 / 200) : ℝ) = ((200 / 269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10380_neg : (423120043 / 1000000000) ≤ -Real.log (131 / 200) ∧
    -Real.log (131 / 200) ≤ (105780011 / 250000000) := by
  have h := checkLog_sound (w := (69 / 331)) (n := 12)
    (lo := (423120043 / 1000000000)) (hi := (105780011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 131) = 1/(131 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10380 : Bounds (-105780011 / 250000000) (-423120043 / 1000000000) (Real.log (131 / 200)) := by
  have h := reflection_log_10380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10381_neg : (17247 / 50000000) ≤ -Real.log (200000 / 200069) ∧
    -Real.log (200000 / 200069) ≤ (344941 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 400069)) (n := 12)
    (lo := (17247 / 50000000)) (hi := (344941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200069 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200069 / 200000) = 1/(200000 / 200069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10381 : Bounds (17247 / 50000000) (344941 / 1000000000) (Real.log (200069 / 200000)) := by
  have h := reflection_log_10381_neg
  have he : Real.log (200069 / 200000) = -Real.log (200000 / 200069) := by
    rw [show ((200069 / 200000) : ℝ) = ((200000 / 200069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10382_neg : (345059 / 1000000000) ≤ -Real.log (199931 / 200000) ∧
    -Real.log (199931 / 200000) ≤ (17253 / 50000000) := by
  have h := checkLog_sound (w := (69 / 399931)) (n := 12)
    (lo := (345059 / 1000000000)) (hi := (17253 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199931) = 1/(199931 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10382 : Bounds (-17253 / 50000000) (-345059 / 1000000000) (Real.log (199931 / 200000)) := by
  have h := reflection_log_10382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10383_neg : (161809277 / 1000000000) ≤ -Real.log (250000 / 293909) ∧
    -Real.log (250000 / 293909) ≤ (80904639 / 500000000) := by
  have h := checkLog_sound (w := (43909 / 543909)) (n := 12)
    (lo := (161809277 / 1000000000)) (hi := (80904639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293909 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293909 / 250000) = 1/(250000 / 293909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10383 : Bounds (161809277 / 1000000000) (80904639 / 500000000) (Real.log (293909 / 250000)) := by
  have h := reflection_log_10383_neg
  have he : Real.log (293909 / 250000) = -Real.log (250000 / 293909) := by
    rw [show ((293909 / 250000) : ℝ) = ((250000 / 293909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10384_neg : (193143099 / 1000000000) ≤ -Real.log (206091 / 250000) ∧
    -Real.log (206091 / 250000) ≤ (1931431 / 10000000) := by
  have h := checkLog_sound (w := (43909 / 456091)) (n := 12)
    (lo := (193143099 / 1000000000)) (hi := (1931431 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 206091) = 1/(206091 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10384 : Bounds (-1931431 / 10000000) (-193143099 / 1000000000) (Real.log (206091 / 250000)) := by
  have h := reflection_log_10384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10385_neg : (162549879 / 1000000000) ≤ -Real.log (1000000 / 1176507) ∧
    -Real.log (1000000 / 1176507) ≤ (4063747 / 25000000) := by
  have h := checkLog_sound (w := (176507 / 2176507)) (n := 12)
    (lo := (162549879 / 1000000000)) (hi := (4063747 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176507 / 1000000) = 1/(1000000 / 1176507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10385 : Bounds (162549879 / 1000000000) (4063747 / 25000000) (Real.log (1176507 / 1000000)) := by
  have h := reflection_log_10385_neg
  have he : Real.log (1176507 / 1000000) = -Real.log (1000000 / 1176507) := by
    rw [show ((1176507 / 1000000) : ℝ) = ((1000000 / 1176507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10386_neg : (194200229 / 1000000000) ≤ -Real.log (823493 / 1000000) ∧
    -Real.log (823493 / 1000000) ≤ (19420023 / 100000000) := by
  have h := checkLog_sound (w := (176507 / 1823493)) (n := 12)
    (lo := (194200229 / 1000000000)) (hi := (19420023 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823493) = 1/(823493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10386 : Bounds (-19420023 / 100000000) (-194200229 / 1000000000) (Real.log (823493 / 1000000)) := by
  have h := reflection_log_10386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10387_neg : (633007 / 20000000) ≤ -Real.log (968845278951 / 1000000000000) ∧
    -Real.log (968845278951 / 1000000000000) ≤ (31650351 / 1000000000) := by
  have h := checkLog_sound (w := (31154721049 / 1968845278951)) (n := 12)
    (lo := (633007 / 20000000)) (hi := (31650351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968845278951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968845278951) = 1/(968845278951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10387 : Bounds (-31650351 / 1000000000) (-633007 / 20000000) (Real.log (968845278951 / 1000000000000)) := by
  have h := reflection_log_10387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10388_neg : (31333821 / 1000000000) ≤ -Real.log (60571999719 / 62500000000) ∧
    -Real.log (60571999719 / 62500000000) ≤ (15666911 / 500000000) := by
  have h := checkLog_sound (w := (1928000281 / 123071999719)) (n := 12)
    (lo := (31333821 / 1000000000)) (hi := (15666911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60571999719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60571999719) = 1/(60571999719 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10388 : Bounds (-15666911 / 500000000) (-31333821 / 1000000000) (Real.log (60571999719 / 62500000000)) := by
  have h := reflection_log_10388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10389_neg : (44369047 / 125000000) ≤ -Real.log (500000000000 / 713056368303) ∧
    -Real.log (500000000000 / 713056368303) ≤ (354952377 / 1000000000) := by
  have h := checkLog_sound (w := (213056368303 / 1213056368303)) (n := 12)
    (lo := (44369047 / 125000000)) (hi := (354952377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713056368303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713056368303 / 500000000000) = 1/(500000000000 / 713056368303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10389 : Bounds (44369047 / 125000000) (354952377 / 1000000000) (Real.log (713056368303 / 500000000000)) := by
  have h := reflection_log_10389_neg
  have he : Real.log (713056368303 / 500000000000) = -Real.log (500000000000 / 713056368303) := by
    rw [show ((713056368303 / 500000000000) : ℝ) = ((500000000000 / 713056368303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10390_neg : (89187527 / 250000000) ≤ -Real.log (125000000000 / 178584851359) ∧
    -Real.log (125000000000 / 178584851359) ≤ (356750109 / 1000000000) := by
  have h := checkLog_sound (w := (53584851359 / 303584851359)) (n := 12)
    (lo := (89187527 / 250000000)) (hi := (356750109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178584851359 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178584851359 / 125000000000) = 1/(125000000000 / 178584851359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10390 : Bounds (89187527 / 250000000) (356750109 / 1000000000) (Real.log (178584851359 / 125000000000)) := by
  have h := reflection_log_10390_neg
  have he : Real.log (178584851359 / 125000000000) = -Real.log (125000000000 / 178584851359) := by
    rw [show ((178584851359 / 125000000000) : ℝ) = ((125000000000 / 178584851359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10391_neg : (717244731 / 1000000000) ≤ -Real.log (250000000000 / 512195121951) ∧
    -Real.log (250000000000 / 512195121951) ≤ (717244733 / 1000000000) := by
  have h := checkLog_sound (w := (12195121951 / 1012195121951)) (n := 12)
    (lo := (24097551 / 1000000000)) (hi := (1506097 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512195121951 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512195121951 / 500000000000) = 1/(250000000000 / 512195121951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10391 : Bounds (717244731 / 1000000000) (717244733 / 1000000000) (Real.log (512195121951 / 250000000000)) := by
  have h := reflection_log_10391_neg
  have he : Real.log (512195121951 / 250000000000) = -Real.log (250000000000 / 512195121951) := by
    rw [show ((512195121951 / 250000000000) : ℝ) = ((250000000000 / 512195121951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10392_neg : (143902811 / 200000000) ≤ -Real.log (125000000000 / 256679389313) ∧
    -Real.log (125000000000 / 256679389313) ≤ (719514057 / 1000000000) := by
  have h := checkLog_sound (w := (6679389313 / 506679389313)) (n := 12)
    (lo := (42187 / 1600000)) (hi := (6591719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256679389313 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256679389313 / 250000000000) = 1/(125000000000 / 256679389313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10392 : Bounds (143902811 / 200000000) (719514057 / 1000000000) (Real.log (256679389313 / 125000000000)) := by
  have h := reflection_log_10392_neg
  have he : Real.log (256679389313 / 125000000000) = -Real.log (125000000000 / 256679389313) := by
    rw [show ((256679389313 / 125000000000) : ℝ) = ((125000000000 / 256679389313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10393_neg : (297137231 / 1000000000) ≤ -Real.log (500 / 673) ∧
    -Real.log (500 / 673) ≤ (18571077 / 62500000) := by
  have h := checkLog_sound (w := (173 / 1173)) (n := 12)
    (lo := (297137231 / 1000000000)) (hi := (18571077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673 / 500) = 1/(500 / 673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10393 : Bounds (297137231 / 1000000000) (18571077 / 62500000) (Real.log (673 / 500)) := by
  have h := reflection_log_10393_neg
  have he : Real.log (673 / 500) = -Real.log (500 / 673) := by
    rw [show ((673 / 500) : ℝ) = ((500 / 673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10394_neg : (424647927 / 1000000000) ≤ -Real.log (327 / 500) ∧
    -Real.log (327 / 500) ≤ (53080991 / 125000000) := by
  have h := checkLog_sound (w := (173 / 827)) (n := 12)
    (lo := (424647927 / 1000000000)) (hi := (53080991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 327) = 1/(327 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10394 : Bounds (-53080991 / 125000000) (-424647927 / 1000000000) (Real.log (327 / 500)) := by
  have h := reflection_log_10394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10395_neg : (17297 / 50000000) ≤ -Real.log (500000 / 500173) ∧
    -Real.log (500000 / 500173) ≤ (345941 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1000173)) (n := 12)
    (lo := (17297 / 50000000)) (hi := (345941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500173 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500173 / 500000) = 1/(500000 / 500173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10395 : Bounds (17297 / 50000000) (345941 / 1000000000) (Real.log (500173 / 500000)) := by
  have h := reflection_log_10395_neg
  have he : Real.log (500173 / 500000) = -Real.log (500000 / 500173) := by
    rw [show ((500173 / 500000) : ℝ) = ((500000 / 500173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10396_neg : (346059 / 1000000000) ≤ -Real.log (499827 / 500000) ∧
    -Real.log (499827 / 500000) ≤ (17303 / 50000000) := by
  have h := checkLog_sound (w := (173 / 999827)) (n := 12)
    (lo := (346059 / 1000000000)) (hi := (17303 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499827) = 1/(499827 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10396 : Bounds (-17303 / 50000000) (-346059 / 1000000000) (Real.log (499827 / 500000)) := by
  have h := reflection_log_10396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10397_neg : (81131273 / 500000000) ≤ -Real.log (1000000 / 1176169) ∧
    -Real.log (1000000 / 1176169) ≤ (162262547 / 1000000000) := by
  have h := checkLog_sound (w := (176169 / 2176169)) (n := 12)
    (lo := (81131273 / 500000000)) (hi := (162262547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176169 / 1000000) = 1/(1000000 / 1176169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10397 : Bounds (81131273 / 500000000) (162262547 / 1000000000) (Real.log (1176169 / 1000000)) := by
  have h := reflection_log_10397_neg
  have he : Real.log (1176169 / 1000000) = -Real.log (1000000 / 1176169) := by
    rw [show ((1176169 / 1000000) : ℝ) = ((1000000 / 1176169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10398_neg : (193789867 / 1000000000) ≤ -Real.log (823831 / 1000000) ∧
    -Real.log (823831 / 1000000) ≤ (48447467 / 250000000) := by
  have h := checkLog_sound (w := (176169 / 1823831)) (n := 12)
    (lo := (193789867 / 1000000000)) (hi := (48447467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823831) = 1/(823831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10398 : Bounds (-48447467 / 250000000) (-193789867 / 1000000000) (Real.log (823831 / 1000000)) := by
  have h := reflection_log_10398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10399_neg : (163004511 / 1000000000) ≤ -Real.log (500000 / 588521) ∧
    -Real.log (500000 / 588521) ≤ (5093891 / 31250000) := by
  have h := checkLog_sound (w := (88521 / 1088521)) (n := 12)
    (lo := (163004511 / 1000000000)) (hi := (5093891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588521 / 500000) = 1/(500000 / 588521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10399 : Bounds (163004511 / 1000000000) (5093891 / 31250000) (Real.log (588521 / 500000)) := by
  have h := reflection_log_10399_neg
  have he : Real.log (588521 / 500000) = -Real.log (500000 / 588521) := by
    rw [show ((588521 / 500000) : ℝ) = ((500000 / 588521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10400_neg : (3044533 / 15625000) ≤ -Real.log (411479 / 500000) ∧
    -Real.log (411479 / 500000) ≤ (194850113 / 1000000000) := by
  have h := checkLog_sound (w := (88521 / 911479)) (n := 12)
    (lo := (3044533 / 15625000)) (hi := (194850113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 411479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 411479) = 1/(411479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10400 : Bounds (-194850113 / 1000000000) (-3044533 / 15625000) (Real.log (411479 / 500000)) := by
  have h := reflection_log_10400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10401_neg : (39807 / 1250000) ≤ -Real.log (242164032559 / 250000000000) ∧
    -Real.log (242164032559 / 250000000000) ≤ (31845601 / 1000000000) := by
  have h := checkLog_sound (w := (7835967441 / 492164032559)) (n := 12)
    (lo := (39807 / 1250000)) (hi := (31845601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242164032559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242164032559) = 1/(242164032559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10401 : Bounds (-31845601 / 1000000000) (-39807 / 1250000) (Real.log (242164032559 / 250000000000)) := by
  have h := reflection_log_10401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10402_neg : (788183 / 25000000) ≤ -Real.log (968964483439 / 1000000000000) ∧
    -Real.log (968964483439 / 1000000000000) ≤ (31527321 / 1000000000) := by
  have h := checkLog_sound (w := (31035516561 / 1968964483439)) (n := 12)
    (lo := (788183 / 25000000)) (hi := (31527321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968964483439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968964483439) = 1/(968964483439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10402 : Bounds (-31527321 / 1000000000) (-788183 / 25000000) (Real.log (968964483439 / 1000000000000)) := by
  have h := reflection_log_10402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10403_neg : (356052413 / 1000000000) ≤ -Real.log (500000000000 / 713841188301) ∧
    -Real.log (500000000000 / 713841188301) ≤ (178026207 / 500000000) := by
  have h := checkLog_sound (w := (213841188301 / 1213841188301)) (n := 12)
    (lo := (356052413 / 1000000000)) (hi := (178026207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713841188301 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713841188301 / 500000000000) = 1/(500000000000 / 713841188301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10403 : Bounds (356052413 / 1000000000) (178026207 / 500000000) (Real.log (713841188301 / 500000000000)) := by
  have h := reflection_log_10403_neg
  have he : Real.log (713841188301 / 500000000000) = -Real.log (500000000000 / 713841188301) := by
    rw [show ((713841188301 / 500000000000) : ℝ) = ((500000000000 / 713841188301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10404_neg : (357854623 / 1000000000) ≤ -Real.log (500000000000 / 715128840111) ∧
    -Real.log (500000000000 / 715128840111) ≤ (11182957 / 31250000) := by
  have h := checkLog_sound (w := (215128840111 / 1215128840111)) (n := 12)
    (lo := (357854623 / 1000000000)) (hi := (11182957 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715128840111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715128840111 / 500000000000) = 1/(500000000000 / 715128840111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10404 : Bounds (357854623 / 1000000000) (11182957 / 31250000) (Real.log (715128840111 / 500000000000)) := by
  have h := reflection_log_10404_neg
  have he : Real.log (715128840111 / 500000000000) = -Real.log (500000000000 / 715128840111) := by
    rw [show ((715128840111 / 500000000000) : ℝ) = ((500000000000 / 715128840111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10405_neg : (143902811 / 200000000) ≤ -Real.log (500000000000 / 1026717557251) ∧
    -Real.log (500000000000 / 1026717557251) ≤ (719514057 / 1000000000) := by
  have h := checkLog_sound (w := (26717557251 / 2026717557251)) (n := 12)
    (lo := (42187 / 1600000)) (hi := (6591719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026717557251 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1026717557251 / 1000000000000) = 1/(500000000000 / 1026717557251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10405 : Bounds (143902811 / 200000000) (719514057 / 1000000000) (Real.log (1026717557251 / 500000000000)) := by
  have h := reflection_log_10405_neg
  have he : Real.log (1026717557251 / 500000000000) = -Real.log (500000000000 / 1026717557251) := by
    rw [show ((1026717557251 / 500000000000) : ℝ) = ((500000000000 / 1026717557251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10406_neg : (360892579 / 500000000) ≤ -Real.log (62500000000 / 128631498471) ∧
    -Real.log (62500000000 / 128631498471) ≤ (18044629 / 25000000) := by
  have h := checkLog_sound (w := (3631498471 / 253631498471)) (n := 12)
    (lo := (14318989 / 500000000)) (hi := (28637979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128631498471 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128631498471 / 125000000000) = 1/(62500000000 / 128631498471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10406 : Bounds (360892579 / 500000000) (18044629 / 25000000) (Real.log (128631498471 / 62500000000)) := by
  have h := reflection_log_10406_neg
  have he : Real.log (128631498471 / 62500000000) = -Real.log (62500000000 / 128631498471) := by
    rw [show ((128631498471 / 62500000000) : ℝ) = ((62500000000 / 128631498471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10407_neg : (297879897 / 1000000000) ≤ -Real.log (1000 / 1347) ∧
    -Real.log (1000 / 1347) ≤ (148939949 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2347)) (n := 12)
    (lo := (297879897 / 1000000000)) (hi := (148939949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347 / 1000) = 1/(1000 / 1347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10407 : Bounds (297879897 / 1000000000) (148939949 / 500000000) (Real.log (1347 / 1000)) := by
  have h := reflection_log_10407_neg
  have he : Real.log (1347 / 1000) = -Real.log (1000 / 1347) := by
    rw [show ((1347 / 1000) : ℝ) = ((1000 / 1347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10408_neg : (426178149 / 1000000000) ≤ -Real.log (653 / 1000) ∧
    -Real.log (653 / 1000) ≤ (8523563 / 20000000) := by
  have h := checkLog_sound (w := (347 / 1653)) (n := 12)
    (lo := (426178149 / 1000000000)) (hi := (8523563 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 653) = 1/(653 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10408 : Bounds (-8523563 / 20000000) (-426178149 / 1000000000) (Real.log (653 / 1000)) := by
  have h := reflection_log_10408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10409_neg : (346939 / 1000000000) ≤ -Real.log (1000000 / 1000347) ∧
    -Real.log (1000000 / 1000347) ≤ (17347 / 50000000) := by
  have h := checkLog_sound (w := (347 / 2000347)) (n := 12)
    (lo := (346939 / 1000000000)) (hi := (17347 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000347 / 1000000) = 1/(1000000 / 1000347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10409 : Bounds (346939 / 1000000000) (17347 / 50000000) (Real.log (1000347 / 1000000)) := by
  have h := reflection_log_10409_neg
  have he : Real.log (1000347 / 1000000) = -Real.log (1000000 / 1000347) := by
    rw [show ((1000347 / 1000000) : ℝ) = ((1000000 / 1000347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10410_neg : (17353 / 50000000) ≤ -Real.log (999653 / 1000000) ∧
    -Real.log (999653 / 1000000) ≤ (347061 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 1999653)) (n := 12)
    (lo := (17353 / 50000000)) (hi := (347061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999653) = 1/(999653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10410 : Bounds (-347061 / 1000000000) (-17353 / 50000000) (Real.log (999653 / 1000000)) := by
  have h := reflection_log_10410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10411_neg : (162716459 / 1000000000) ≤ -Real.log (1000000 / 1176703) ∧
    -Real.log (1000000 / 1176703) ≤ (8135823 / 50000000) := by
  have h := checkLog_sound (w := (176703 / 2176703)) (n := 12)
    (lo := (162716459 / 1000000000)) (hi := (8135823 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176703 / 1000000) = 1/(1000000 / 1176703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10411 : Bounds (162716459 / 1000000000) (8135823 / 50000000) (Real.log (1176703 / 1000000)) := by
  have h := reflection_log_10411_neg
  have he : Real.log (1176703 / 1000000) = -Real.log (1000000 / 1176703) := by
    rw [show ((1176703 / 1000000) : ℝ) = ((1000000 / 1176703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10412_neg : (48609567 / 250000000) ≤ -Real.log (823297 / 1000000) ∧
    -Real.log (823297 / 1000000) ≤ (194438269 / 1000000000) := by
  have h := checkLog_sound (w := (176703 / 1823297)) (n := 12)
    (lo := (48609567 / 250000000)) (hi := (194438269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823297) = 1/(823297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10412 : Bounds (-194438269 / 1000000000) (-48609567 / 250000000) (Real.log (823297 / 1000000)) := by
  have h := reflection_log_10412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10413_neg : (163458937 / 1000000000) ≤ -Real.log (1000000 / 1177577) ∧
    -Real.log (1000000 / 1177577) ≤ (81729469 / 500000000) := by
  have h := checkLog_sound (w := (177577 / 2177577)) (n := 12)
    (lo := (163458937 / 1000000000)) (hi := (81729469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177577 / 1000000) = 1/(1000000 / 1177577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10413 : Bounds (163458937 / 1000000000) (81729469 / 500000000) (Real.log (1177577 / 1000000)) := by
  have h := reflection_log_10413_neg
  have he : Real.log (1177577 / 1000000) = -Real.log (1000000 / 1177577) := by
    rw [show ((1177577 / 1000000) : ℝ) = ((1000000 / 1177577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10414_neg : (195500417 / 1000000000) ≤ -Real.log (822423 / 1000000) ∧
    -Real.log (822423 / 1000000) ≤ (97750209 / 500000000) := by
  have h := checkLog_sound (w := (177577 / 1822423)) (n := 12)
    (lo := (195500417 / 1000000000)) (hi := (97750209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822423) = 1/(822423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10414 : Bounds (-97750209 / 500000000) (-195500417 / 1000000000) (Real.log (822423 / 1000000)) := by
  have h := reflection_log_10414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10415_neg : (801037 / 25000000) ≤ -Real.log (968466409071 / 1000000000000) ∧
    -Real.log (968466409071 / 1000000000000) ≤ (32041481 / 1000000000) := by
  have h := checkLog_sound (w := (31533590929 / 1968466409071)) (n := 12)
    (lo := (801037 / 25000000)) (hi := (32041481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968466409071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968466409071) = 1/(968466409071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10415 : Bounds (-32041481 / 1000000000) (-801037 / 25000000) (Real.log (968466409071 / 1000000000000)) := by
  have h := reflection_log_10415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10416_neg : (1982613 / 62500000) ≤ -Real.log (968776049791 / 1000000000000) ∧
    -Real.log (968776049791 / 1000000000000) ≤ (31721809 / 1000000000) := by
  have h := checkLog_sound (w := (31223950209 / 1968776049791)) (n := 12)
    (lo := (1982613 / 62500000)) (hi := (31721809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968776049791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968776049791) = 1/(968776049791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10416 : Bounds (-31721809 / 1000000000) (-1982613 / 62500000) (Real.log (968776049791 / 1000000000000)) := by
  have h := reflection_log_10416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10417_neg : (44644341 / 125000000) ≤ -Real.log (2500000000 / 3573142499) ∧
    -Real.log (2500000000 / 3573142499) ≤ (357154729 / 1000000000) := by
  have h := checkLog_sound (w := (1073142499 / 6073142499)) (n := 12)
    (lo := (44644341 / 125000000)) (hi := (357154729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3573142499 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3573142499 / 2500000000) = 1/(2500000000 / 3573142499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10417 : Bounds (44644341 / 125000000) (357154729 / 1000000000) (Real.log (3573142499 / 2500000000)) := by
  have h := reflection_log_10417_neg
  have he : Real.log (3573142499 / 2500000000) = -Real.log (2500000000 / 3573142499) := by
    rw [show ((3573142499 / 2500000000) : ℝ) = ((2500000000 / 3573142499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10418_neg : (71791871 / 200000000) ≤ -Real.log (125000000000 / 178979825467) ∧
    -Real.log (125000000000 / 178979825467) ≤ (89739839 / 250000000) := by
  have h := checkLog_sound (w := (53979825467 / 303979825467)) (n := 12)
    (lo := (71791871 / 200000000)) (hi := (89739839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178979825467 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178979825467 / 125000000000) = 1/(125000000000 / 178979825467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10418 : Bounds (71791871 / 200000000) (89739839 / 250000000) (Real.log (178979825467 / 125000000000)) := by
  have h := reflection_log_10418_neg
  have he : Real.log (178979825467 / 125000000000) = -Real.log (125000000000 / 178979825467) := by
    rw [show ((178979825467 / 125000000000) : ℝ) = ((125000000000 / 178979825467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10419_neg : (360892579 / 500000000) ≤ -Real.log (500000000000 / 1029051987767) ∧
    -Real.log (500000000000 / 1029051987767) ≤ (18044629 / 25000000) := by
  have h := checkLog_sound (w := (29051987767 / 2029051987767)) (n := 12)
    (lo := (14318989 / 500000000)) (hi := (28637979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1029051987767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1029051987767 / 1000000000000) = 1/(500000000000 / 1029051987767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10419 : Bounds (360892579 / 500000000) (18044629 / 25000000) (Real.log (1029051987767 / 500000000000)) := by
  have h := reflection_log_10419_neg
  have he : Real.log (1029051987767 / 500000000000) = -Real.log (500000000000 / 1029051987767) := by
    rw [show ((1029051987767 / 500000000000) : ℝ) = ((500000000000 / 1029051987767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10420_neg : (362029023 / 500000000) ≤ -Real.log (125000000000 / 257848392037) ∧
    -Real.log (125000000000 / 257848392037) ≤ (11313407 / 15625000) := by
  have h := checkLog_sound (w := (7848392037 / 507848392037)) (n := 12)
    (lo := (15455433 / 500000000)) (hi := (30910867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257848392037 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(257848392037 / 250000000000) = 1/(125000000000 / 257848392037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10420 : Bounds (362029023 / 500000000) (11313407 / 15625000) (Real.log (257848392037 / 125000000000)) := by
  have h := reflection_log_10420_neg
  have he : Real.log (257848392037 / 125000000000) = -Real.log (125000000000 / 257848392037) := by
    rw [show ((257848392037 / 125000000000) : ℝ) = ((125000000000 / 257848392037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10421_neg : (74655503 / 250000000) ≤ -Real.log (250 / 337) ∧
    -Real.log (250 / 337) ≤ (298622013 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 587)) (n := 12)
    (lo := (74655503 / 250000000)) (hi := (298622013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337 / 250) = 1/(250 / 337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10421 : Bounds (74655503 / 250000000) (298622013 / 1000000000) (Real.log (337 / 250)) := by
  have h := reflection_log_10421_neg
  have he : Real.log (337 / 250) = -Real.log (250 / 337) := by
    rw [show ((337 / 250) : ℝ) = ((250 / 337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10422_neg : (427710717 / 1000000000) ≤ -Real.log (163 / 250) ∧
    -Real.log (163 / 250) ≤ (213855359 / 500000000) := by
  have h := checkLog_sound (w := (87 / 413)) (n := 12)
    (lo := (427710717 / 1000000000)) (hi := (213855359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 163) = 1/(163 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10422 : Bounds (-213855359 / 500000000) (-427710717 / 1000000000) (Real.log (163 / 250)) := by
  have h := reflection_log_10422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10423_neg : (347939 / 1000000000) ≤ -Real.log (250000 / 250087) ∧
    -Real.log (250000 / 250087) ≤ (17397 / 50000000) := by
  have h := checkLog_sound (w := (87 / 500087)) (n := 12)
    (lo := (347939 / 1000000000)) (hi := (17397 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250087 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250087 / 250000) = 1/(250000 / 250087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10423 : Bounds (347939 / 1000000000) (17397 / 50000000) (Real.log (250087 / 250000)) := by
  have h := reflection_log_10423_neg
  have he : Real.log (250087 / 250000) = -Real.log (250000 / 250087) := by
    rw [show ((250087 / 250000) : ℝ) = ((250000 / 250087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10424_neg : (17403 / 50000000) ≤ -Real.log (249913 / 250000) ∧
    -Real.log (249913 / 250000) ≤ (348061 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 499913)) (n := 12)
    (lo := (17403 / 50000000)) (hi := (348061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249913) = 1/(249913 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10424 : Bounds (-348061 / 1000000000) (-17403 / 50000000) (Real.log (249913 / 250000)) := by
  have h := reflection_log_10424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10425_neg : (163170167 / 1000000000) ≤ -Real.log (1000000 / 1177237) ∧
    -Real.log (1000000 / 1177237) ≤ (20396271 / 125000000) := by
  have h := checkLog_sound (w := (177237 / 2177237)) (n := 12)
    (lo := (163170167 / 1000000000)) (hi := (20396271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177237 / 1000000) = 1/(1000000 / 1177237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10425 : Bounds (163170167 / 1000000000) (20396271 / 125000000) (Real.log (1177237 / 1000000)) := by
  have h := reflection_log_10425_neg
  have he : Real.log (1177237 / 1000000) = -Real.log (1000000 / 1177237) := by
    rw [show ((1177237 / 1000000) : ℝ) = ((1000000 / 1177237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10426_neg : (19508709 / 100000000) ≤ -Real.log (822763 / 1000000) ∧
    -Real.log (822763 / 1000000) ≤ (195087091 / 1000000000) := by
  have h := checkLog_sound (w := (177237 / 1822763)) (n := 12)
    (lo := (19508709 / 100000000)) (hi := (195087091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822763) = 1/(822763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10426 : Bounds (-195087091 / 1000000000) (-19508709 / 100000000) (Real.log (822763 / 1000000)) := by
  have h := reflection_log_10426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10427_neg : (163913157 / 1000000000) ≤ -Real.log (15625 / 18408) ∧
    -Real.log (15625 / 18408) ≤ (81956579 / 500000000) := by
  have h := checkLog_sound (w := (2783 / 34033)) (n := 12)
    (lo := (163913157 / 1000000000)) (hi := (81956579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18408 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18408 / 15625) = 1/(15625 / 18408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10427 : Bounds (163913157 / 1000000000) (81956579 / 500000000) (Real.log (18408 / 15625)) := by
  have h := reflection_log_10427_neg
  have he : Real.log (18408 / 15625) = -Real.log (15625 / 18408) := by
    rw [show ((18408 / 15625) : ℝ) = ((15625 / 18408) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10428_neg : (98075573 / 500000000) ≤ -Real.log (12842 / 15625) ∧
    -Real.log (12842 / 15625) ≤ (196151147 / 1000000000) := by
  have h := checkLog_sound (w := (2783 / 28467)) (n := 12)
    (lo := (98075573 / 500000000)) (hi := (196151147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12842) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12842) = 1/(12842 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10428 : Bounds (-196151147 / 1000000000) (-98075573 / 500000000) (Real.log (12842 / 15625)) := by
  have h := reflection_log_10428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10429_neg : (32237989 / 1000000000) ≤ -Real.log (236395536 / 244140625) ∧
    -Real.log (236395536 / 244140625) ≤ (3223799 / 100000000) := by
  have h := checkLog_sound (w := (7745089 / 480536161)) (n := 12)
    (lo := (32237989 / 1000000000)) (hi := (3223799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 236395536) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 236395536) = 1/(236395536 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10429 : Bounds (-3223799 / 100000000) (-32237989 / 1000000000) (Real.log (236395536 / 244140625)) := by
  have h := reflection_log_10429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10430_neg : (31916923 / 1000000000) ≤ -Real.log (968587045831 / 1000000000000) ∧
    -Real.log (968587045831 / 1000000000000) ≤ (7979231 / 250000000) := by
  have h := checkLog_sound (w := (31412954169 / 1968587045831)) (n := 12)
    (lo := (31916923 / 1000000000)) (hi := (7979231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968587045831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968587045831) = 1/(968587045831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10430 : Bounds (-7979231 / 250000000) (-31916923 / 1000000000) (Real.log (968587045831 / 1000000000000)) := by
  have h := reflection_log_10430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10431_neg : (179128629 / 500000000) ≤ -Real.log (390625000 / 558919401) ∧
    -Real.log (390625000 / 558919401) ≤ (358257259 / 1000000000) := by
  have h := checkLog_sound (w := (168294401 / 949544401)) (n := 12)
    (lo := (179128629 / 500000000)) (hi := (358257259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558919401 / 390625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558919401 / 390625000) = 1/(390625000 / 558919401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10431 : Bounds (179128629 / 500000000) (358257259 / 1000000000) (Real.log (558919401 / 390625000)) := by
  have h := reflection_log_10431_neg
  have he : Real.log (558919401 / 390625000) = -Real.log (390625000 / 558919401) := by
    rw [show ((558919401 / 390625000) : ℝ) = ((390625000 / 558919401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


