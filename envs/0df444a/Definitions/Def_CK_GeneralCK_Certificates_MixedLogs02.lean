-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLogs02
-- name    : CK_GeneralCK_Certificates_MixedLogs02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:22:57.718204+00:00
-- url     : https://prove2.me/theorems/6821ea01-1d11-4287-a1b9-f598dcce7101
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLogs02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLogs02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLogs02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLogs02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLogs02.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_v_32 : (267745237 / 125000000) ≤ -Real.log (31 / 264) ∧
    -Real.log (31 / 264) ≤ (21419619 / 10000000) := by
  have h := checkLog_sound (w := (1 / 32)) (n := 12)
    (lo := (15630089 / 250000000)) (hi := (62520357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33 / 31) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(33 / 31) = 1/(31 / 264) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_32 : (124910649 / 1000000000) ≤ -Real.log (233 / 264) ∧
    -Real.log (233 / 264) ≤ (2498213 / 20000000) := by
  have h := checkLog_sound (w := (31 / 497)) (n := 12)
    (lo := (124910649 / 1000000000)) (hi := (2498213 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264 / 233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(264 / 233) = 1/(233 / 264) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_33 : (424597957 / 200000000) ≤ -Real.log (337 / 2816) ∧
    -Real.log (337 / 2816) ≤ (2122989789 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 689)) (n := 12)
    (lo := (8709649 / 200000000)) (hi := (21774123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 337) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(352 / 337) = 1/(337 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_33 : (25492437 / 200000000) ≤ -Real.log (2479 / 2816) ∧
    -Real.log (2479 / 2816) ≤ (63731093 / 500000000) := by
  have h := checkLog_sound (w := (337 / 5295)) (n := 12)
    (lo := (25492437 / 200000000)) (hi := (63731093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2479) = 1/(2479 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_34 : (2104370923 / 1000000000) ≤ -Real.log (515 / 4224) ∧
    -Real.log (515 / 4224) ≤ (2104370927 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 1043)) (n := 12)
    (lo := (24929383 / 1000000000)) (hi := (3116173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 515) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(528 / 515) = 1/(515 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_34 : (130020247 / 1000000000) ≤ -Real.log (3709 / 4224) ∧
    -Real.log (3709 / 4224) ≤ (16252531 / 125000000) := by
  have h := checkLog_sound (w := (515 / 7933)) (n := 12)
    (lo := (130020247 / 1000000000)) (hi := (16252531 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3709) = 1/(3709 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_35 : (417218479 / 200000000) ≤ -Real.log (1049 / 8448) ∧
    -Real.log (1049 / 8448) ≤ (2086092399 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 2105)) (n := 12)
    (lo := (1330171 / 200000000)) (hi := (831357 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 1049) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 1049) = 1/(1049 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_35 : (132584871 / 1000000000) ≤ -Real.log (7399 / 8448) ∧
    -Real.log (7399 / 8448) ≤ (16573109 / 125000000) := by
  have h := checkLog_sound (w := (1049 / 15847)) (n := 12)
    (lo := (132584871 / 1000000000)) (hi := (16573109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7399) = 1/(7399 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_36 : (413628397 / 200000000) ≤ -Real.log (89 / 704) ∧
    -Real.log (89 / 704) ≤ (517035497 / 250000000) := by
  have h := checkLog_sound (w := (87 / 265)) (n := 12)
    (lo := (5454781 / 8000000)) (hi := (340923813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 89) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(176 / 89) = 1/(89 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_36 : (16894511 / 125000000) ≤ -Real.log (615 / 704) ∧
    -Real.log (615 / 704) ≤ (135156089 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 1319)) (n := 12)
    (lo := (16894511 / 125000000)) (hi := (135156089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704 / 615) = 1/(615 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_37 : (2050508117 / 1000000000) ≤ -Real.log (1087 / 8448) ∧
    -Real.log (1087 / 8448) ≤ (51262703 / 25000000) := by
  have h := checkLog_sound (w := (1025 / 3199)) (n := 12)
    (lo := (664213757 / 1000000000)) (hi := (332106879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1087) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1087) = 1/(1087 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_37 : (137733933 / 1000000000) ≤ -Real.log (7361 / 8448) ∧
    -Real.log (7361 / 8448) ≤ (68866967 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 15809)) (n := 12)
    (lo := (137733933 / 1000000000)) (hi := (68866967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7361) = 1/(7361 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_38 : (1016589911 / 500000000) ≤ -Real.log (553 / 4224) ∧
    -Real.log (553 / 4224) ≤ (81327193 / 40000000) := by
  have h := checkLog_sound (w := (503 / 1609)) (n := 12)
    (lo := (323442731 / 500000000)) (hi := (646885463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 553) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 553) = 1/(553 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_38 : (140318441 / 1000000000) ≤ -Real.log (3671 / 4224) ∧
    -Real.log (3671 / 4224) ≤ (70159221 / 500000000) := by
  have h := checkLog_sound (w := (553 / 7895)) (n := 12)
    (lo := (140318441 / 1000000000)) (hi := (70159221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3671) = 1/(3671 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_39 : (201614669 / 100000000) ≤ -Real.log (375 / 2816) ∧
    -Real.log (375 / 2816) ≤ (2016146693 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 1079)) (n := 12)
    (lo := (62985233 / 100000000)) (hi := (629852331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 375) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 375) = 1/(375 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_39 : (71454823 / 500000000) ≤ -Real.log (2441 / 2816) ∧
    -Real.log (2441 / 2816) ≤ (142909647 / 1000000000) := by
  have h := checkLog_sound (w := (375 / 5257)) (n := 12)
    (lo := (71454823 / 500000000)) (hi := (142909647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2441) = 1/(2441 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_40 : (124962427 / 62500000) ≤ -Real.log (13 / 96) ∧
    -Real.log (13 / 96) ≤ (399879767 / 200000000) := by
  have h := checkLog_sound (w := (11 / 37)) (n := 12)
    (lo := (76638059 / 125000000)) (hi := (613104473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24 / 13) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(24 / 13) = 1/(13 / 96) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_40 : (145507583 / 1000000000) ≤ -Real.log (83 / 96) ∧
    -Real.log (83 / 96) ≤ (568389 / 3906250) := by
  have h := checkLog_sound (w := (13 / 179)) (n := 12)
    (lo := (145507583 / 1000000000)) (hi := (568389 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96 / 83) = 1/(83 / 96) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_41 : (495731713 / 250000000) ≤ -Real.log (1163 / 8448) ∧
    -Real.log (1163 / 8448) ≤ (396585371 / 200000000) := by
  have h := checkLog_sound (w := (949 / 3275)) (n := 12)
    (lo := (149158123 / 250000000)) (hi := (596632493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1163) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1163) = 1/(1163 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_41 : (148112287 / 1000000000) ≤ -Real.log (7285 / 8448) ∧
    -Real.log (7285 / 8448) ≤ (4628509 / 31250000) := by
  have h := checkLog_sound (w := (1163 / 15733)) (n := 12)
    (lo := (148112287 / 1000000000)) (hi := (4628509 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7285) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7285) = 1/(7285 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_42 : (983360903 / 500000000) ≤ -Real.log (197 / 1408) ∧
    -Real.log (197 / 1408) ≤ (1966721809 / 1000000000) := by
  have h := checkLog_sound (w := (155 / 549)) (n := 12)
    (lo := (290213723 / 500000000)) (hi := (580427447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 197) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(352 / 197) = 1/(197 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_42 : (150723793 / 1000000000) ≤ -Real.log (1211 / 1408) ∧
    -Real.log (1211 / 1408) ≤ (75361897 / 500000000) := by
  have h := checkLog_sound (w := (197 / 2619)) (n := 12)
    (lo := (150723793 / 1000000000)) (hi := (75361897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1211) = 1/(1211 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_43 : (975387591 / 500000000) ≤ -Real.log (1201 / 8448) ∧
    -Real.log (1201 / 8448) ≤ (390155037 / 200000000) := by
  have h := checkLog_sound (w := (911 / 3313)) (n := 12)
    (lo := (282240411 / 500000000)) (hi := (564480823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1201) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1201) = 1/(1201 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_43 : (19167767 / 125000000) ≤ -Real.log (7247 / 8448) ∧
    -Real.log (7247 / 8448) ≤ (153342137 / 1000000000) := by
  have h := checkLog_sound (w := (1201 / 15695)) (n := 12)
    (lo := (19167767 / 125000000)) (hi := (153342137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7247) = 1/(7247 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_44 : (1935078867 / 1000000000) ≤ -Real.log (305 / 2112) ∧
    -Real.log (305 / 2112) ≤ (193507887 / 100000000) := by
  have h := checkLog_sound (w := (223 / 833)) (n := 12)
    (lo := (548784507 / 1000000000)) (hi := (137196127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 305) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(528 / 305) = 1/(305 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_44 : (77983677 / 500000000) ≤ -Real.log (1807 / 2112) ∧
    -Real.log (1807 / 2112) ≤ (31193471 / 200000000) := by
  have h := checkLog_sound (w := (305 / 3919)) (n := 12)
    (lo := (77983677 / 500000000)) (hi := (31193471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1807) = 1/(1807 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_45 : (1919625123 / 1000000000) ≤ -Real.log (413 / 2816) ∧
    -Real.log (413 / 2816) ≤ (959812563 / 500000000) := by
  have h := checkLog_sound (w := (291 / 1117)) (n := 12)
    (lo := (533330763 / 1000000000)) (hi := (133332691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 413) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 413) = 1/(413 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_45 : (158599481 / 1000000000) ≤ -Real.log (2403 / 2816) ∧
    -Real.log (2403 / 2816) ≤ (79299741 / 500000000) := by
  have h := checkLog_sound (w := (413 / 5219)) (n := 12)
    (lo := (158599481 / 1000000000)) (hi := (79299741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2403) = 1/(2403 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_46 : (1904406567 / 1000000000) ≤ -Real.log (629 / 4224) ∧
    -Real.log (629 / 4224) ≤ (190440657 / 100000000) := by
  have h := checkLog_sound (w := (427 / 1685)) (n := 12)
    (lo := (518112207 / 1000000000)) (hi := (32382013 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 629) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 629) = 1/(629 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_46 : (32247711 / 200000000) ≤ -Real.log (3595 / 4224) ∧
    -Real.log (3595 / 4224) ≤ (40309639 / 250000000) := by
  have h := checkLog_sound (w := (629 / 7819)) (n := 12)
    (lo := (32247711 / 200000000)) (hi := (40309639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3595) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3595) = 1/(3595 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_47 : (472354037 / 250000000) ≤ -Real.log (1277 / 8448) ∧
    -Real.log (1277 / 8448) ≤ (1889416151 / 1000000000) := by
  have h := checkLog_sound (w := (835 / 3389)) (n := 12)
    (lo := (125780447 / 250000000)) (hi := (503121789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1277) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1277) = 1/(1277 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_47 : (40971153 / 250000000) ≤ -Real.log (7171 / 8448) ∧
    -Real.log (7171 / 8448) ≤ (163884613 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 15619)) (n := 12)
    (lo := (40971153 / 250000000)) (hi := (163884613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7171) = 1/(7171 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

end GeneralCK.Certificates.Mixed


