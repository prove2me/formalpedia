-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs04
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:47:03.232513+00:00
-- url     : https://prove2.me/theorems/4905843a-58d0-4824-a4b1-74eb4505853d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs04` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs04` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs04` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs04 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs04.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_64 : (83515393 / 20000000) ≤ -Real.log (37757 / 2457600) ∧
    -Real.log (37757 / 2457600) ≤ (4175769657 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 76157)) (n := 12)
    (lo := (1688657 / 100000000)) (hi := (16886571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 37757) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 37757) = 1/(37757 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_64 : (15482601 / 1000000000) ≤ -Real.log (2419843 / 2457600) ∧
    -Real.log (2419843 / 2457600) ≤ (7741301 / 500000000) := by
  have h := checkLog_sound (w := (37757 / 4877443)) (n := 12)
    (lo := (15482601 / 1000000000)) (hi := (7741301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2419843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2419843) = 1/(2419843 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_64 : (520035881 / 250000000) ≤ xi (37757 / 2457600) ∧ xi (37757 / 2457600) ≤ (260017941 / 125000000) ∧
    (4191252251 / 2000000000) ≤ kap (37757 / 2457600) ∧ kap (37757 / 2457600) ≤ (4191252259 / 2000000000) := by
  have h := endpoint_bounds (v := ((37757 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_64.1 (by convert! log_c_64.1 using 1; norm_num)
    log_v_64.2 (by convert! log_c_64.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_65 : (4168670403 / 1000000000) ≤ -Real.log (19013 / 1228800) ∧
    -Real.log (19013 / 1228800) ≤ (416867041 / 100000000) := by
  have h := checkLog_sound (w := (187 / 38213)) (n := 12)
    (lo := (9787323 / 1000000000)) (hi := (2446831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 19013) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19200 / 19013) = 1/(19013 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_65 : (3898443 / 250000000) ≤ -Real.log (1209787 / 1228800) ∧
    -Real.log (1209787 / 1228800) ≤ (15593773 / 1000000000) := by
  have h := checkLog_sound (w := (19013 / 2438587)) (n := 12)
    (lo := (3898443 / 250000000)) (hi := (15593773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1209787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1209787) = 1/(1209787 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_65 : (415307663 / 200000000) ≤ xi (19013 / 1228800) ∧ xi (19013 / 1228800) ≤ (2076538319 / 1000000000) ∧
    (167370567 / 80000000) ≤ kap (19013 / 1228800) ∧ kap (19013 / 1228800) ≤ (4184264183 / 2000000000) := by
  have h := endpoint_bounds (v := ((19013 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_65.1 (by convert! log_c_65.1 using 1; norm_num)
    log_v_65.2 (by convert! log_c_65.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_66 : (10404053 / 2500000) ≤ -Real.log (2553 / 163840) ∧
    -Real.log (2553 / 163840) ≤ (4161621207 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 5113)) (n := 12)
    (lo := (68453 / 25000000)) (hi := (2738121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2553) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2560 / 2553) = 1/(2553 / 163840) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_66 : (3140991 / 200000000) ≤ -Real.log (161287 / 163840) ∧
    -Real.log (161287 / 163840) ≤ (3926239 / 250000000) := by
  have h := checkLog_sound (w := (2553 / 325127)) (n := 12)
    (lo := (3140991 / 200000000)) (hi := (3926239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163840 / 161287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163840 / 161287) = 1/(161287 / 163840) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_66 : (1036479061 / 500000000) ≤ xi (2553 / 163840) ∧ xi (2553 / 163840) ≤ (1036479063 / 500000000) ∧
    (835465231 / 400000000) ≤ kap (2553 / 163840) ∧ kap (2553 / 163840) ≤ (4177326163 / 2000000000) := by
  have h := endpoint_bounds (v := ((2553 / 163840) : ℝ)) (by norm_num) (by norm_num)
    log_v_66.1 (by convert! log_c_66.1 using 1; norm_num)
    log_v_66.2 (by convert! log_c_66.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_67 : (4154621341 / 1000000000) ≤ -Real.log (9641 / 614400) ∧
    -Real.log (9641 / 614400) ≤ (4154621347 / 1000000000) := by
  have h := checkLog_sound (w := (9559 / 28841)) (n := 12)
    (lo := (688885441 / 1000000000)) (hi := (344442721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 9641) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 9641) = 1/(9641 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_67 : (316323 / 20000000) ≤ -Real.log (604759 / 614400) ∧
    -Real.log (604759 / 614400) ≤ (15816151 / 1000000000) := by
  have h := checkLog_sound (w := (9641 / 1219159)) (n := 12)
    (lo := (316323 / 20000000)) (hi := (15816151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 604759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 604759) = 1/(604759 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_67 : (413880519 / 200000000) ≤ xi (9641 / 614400) ∧ xi (9641 / 614400) ≤ (4138805197 / 2000000000) ∧
    (4170437491 / 2000000000) ≤ kap (9641 / 614400) ∧ kap (9641 / 614400) ≤ (2085218749 / 1000000000) := by
  have h := endpoint_bounds (v := ((9641 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_67.1 (by convert! log_c_67.1 using 1; norm_num)
    log_v_67.2 (by convert! log_c_67.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_68 : (4147670139 / 1000000000) ≤ -Real.log (38833 / 2457600) ∧
    -Real.log (38833 / 2457600) ≤ (829534029 / 200000000) := by
  have h := checkLog_sound (w := (37967 / 115633)) (n := 12)
    (lo := (681934239 / 1000000000)) (hi := (4262089 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 38833) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(76800 / 38833) = 1/(38833 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_68 : (15927357 / 1000000000) ≤ -Real.log (2418767 / 2457600) ∧
    -Real.log (2418767 / 2457600) ≤ (7963679 / 500000000) := by
  have h := checkLog_sound (w := (38833 / 4876367)) (n := 12)
    (lo := (15927357 / 1000000000)) (hi := (7963679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2418767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2418767) = 1/(2418767 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_68 : (4131742781 / 2000000000) ≤ xi (38833 / 2457600) ∧ xi (38833 / 2457600) ≤ (1032935697 / 500000000) ∧
    (520449687 / 250000000) ≤ kap (38833 / 2457600) ∧ kap (38833 / 2457600) ≤ (4163597503 / 2000000000) := by
  have h := endpoint_bounds (v := ((38833 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_68.1 (by convert! log_c_68.1 using 1; norm_num)
    log_v_68.2 (by convert! log_c_68.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_69 : (4140766923 / 1000000000) ≤ -Real.log (6517 / 409600) ∧
    -Real.log (6517 / 409600) ≤ (4140766929 / 1000000000) := by
  have h := checkLog_sound (w := (6283 / 19317)) (n := 12)
    (lo := (675031023 / 1000000000)) (hi := (42189439 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 6517) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 6517) = 1/(6517 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_69 : (16038577 / 1000000000) ≤ -Real.log (403083 / 409600) ∧
    -Real.log (403083 / 409600) ≤ (8019289 / 500000000) := by
  have h := checkLog_sound (w := (6517 / 812683)) (n := 12)
    (lo := (16038577 / 1000000000)) (hi := (8019289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 403083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 403083) = 1/(403083 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_69 : (824945669 / 400000000) ≤ xi (6517 / 409600) ∧ xi (6517 / 409600) ≤ (128897761 / 62500000) ∧
    (8313611 / 4000000) ≤ kap (6517 / 409600) ∧ kap (6517 / 409600) ≤ (4156805507 / 2000000000) := by
  have h := endpoint_bounds (v := ((6517 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_69.1 (by convert! log_c_69.1 using 1; norm_num)
    log_v_69.2 (by convert! log_c_69.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_70 : (826782207 / 200000000) ≤ -Real.log (39371 / 2457600) ∧
    -Real.log (39371 / 2457600) ≤ (4133911041 / 1000000000) := by
  have h := checkLog_sound (w := (37429 / 116171)) (n := 12)
    (lo := (133635027 / 200000000)) (hi := (20880473 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 39371) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(76800 / 39371) = 1/(39371 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_70 : (16149809 / 1000000000) ≤ -Real.log (2418229 / 2457600) ∧
    -Real.log (2418229 / 2457600) ≤ (1614981 / 100000000) := by
  have h := checkLog_sound (w := (39371 / 4875829)) (n := 12)
    (lo := (16149809 / 1000000000)) (hi := (1614981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2418229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2418229) = 1/(2418229 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_70 : (164710449 / 80000000) ≤ xi (39371 / 2457600) ∧ xi (39371 / 2457600) ≤ (257360077 / 125000000) ∧
    (1037515211 / 500000000) ≤ kap (39371 / 2457600) ∧ kap (39371 / 2457600) ≤ (4150060851 / 2000000000) := by
  have h := endpoint_bounds (v := ((39371 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_70.1 (by convert! log_c_70.1 using 1; norm_num)
    log_v_70.2 (by convert! log_c_70.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_71 : (412710183 / 100000000) ≤ -Real.log (991 / 61440) ∧
    -Real.log (991 / 61440) ≤ (1031775459 / 250000000) := by
  have h := checkLog_sound (w := (929 / 2911)) (n := 12)
    (lo := (66136593 / 100000000)) (hi := (661365931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920 / 991) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1920 / 991) = 1/(991 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_71 : (8130527 / 500000000) ≤ -Real.log (60449 / 61440) ∧
    -Real.log (60449 / 61440) ≤ (3252211 / 200000000) := by
  have h := checkLog_sound (w := (991 / 121889)) (n := 12)
    (lo := (8130527 / 500000000)) (hi := (3252211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61440 / 60449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61440 / 60449) = 1/(60449 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_71 : (164433631 / 80000000) ≤ xi (991 / 61440) ∧ xi (991 / 61440) ≤ (2055420391 / 1000000000) ∧
    (1035840721 / 500000000) ≤ kap (991 / 61440) ∧ kap (991 / 61440) ≤ (4143362891 / 2000000000) := by
  have h := endpoint_bounds (v := ((991 / 61440) : ℝ)) (by norm_num) (by norm_num)
    log_v_71.1 (by convert! log_c_71.1 using 1; norm_num)
    log_v_71.2 (by convert! log_c_71.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_72 : (4120338677 / 1000000000) ≤ -Real.log (13303 / 819200) ∧
    -Real.log (13303 / 819200) ≤ (4120338683 / 1000000000) := by
  have h := checkLog_sound (w := (12297 / 38903)) (n := 12)
    (lo := (654602777 / 1000000000)) (hi := (327301389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 13303) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25600 / 13303) = 1/(13303 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_72 : (16372311 / 1000000000) ≤ -Real.log (805897 / 819200) ∧
    -Real.log (805897 / 819200) ≤ (2046539 / 125000000) := by
  have h := checkLog_sound (w := (13303 / 1625097)) (n := 12)
    (lo := (16372311 / 1000000000)) (hi := (2046539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 805897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 805897) = 1/(805897 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_72 : (820793273 / 400000000) ≤ xi (13303 / 819200) ∧ xi (13303 / 819200) ≤ (1025991593 / 500000000) ∧
    (1034177747 / 500000000) ≤ kap (13303 / 819200) ∧ kap (13303 / 819200) ≤ (827342199 / 400000000) := by
  have h := endpoint_bounds (v := ((13303 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_72.1 (by convert! log_c_72.1 using 1; norm_num)
    log_v_72.2 (by convert! log_c_72.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_73 : (2056810479 / 500000000) ≤ -Real.log (20089 / 1228800) ∧
    -Real.log (20089 / 1228800) ≤ (1028405241 / 250000000) := by
  have h := checkLog_sound (w := (18311 / 58489)) (n := 12)
    (lo := (323942529 / 500000000)) (hi := (647885059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 20089) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 20089) = 1/(20089 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_73 : (824179 / 50000000) ≤ -Real.log (1208711 / 1228800) ∧
    -Real.log (1208711 / 1228800) ≤ (16483581 / 1000000000) := by
  have h := checkLog_sound (w := (20089 / 2437511)) (n := 12)
    (lo := (824179 / 50000000)) (hi := (16483581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1208711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1208711) = 1/(1208711 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_73 : (4097137377 / 2000000000) ≤ xi (20089 / 1228800) ∧ xi (20089 / 1228800) ≤ (512142173 / 250000000) ∧
    (2065052269 / 1000000000) ≤ kap (20089 / 1228800) ∧ kap (20089 / 1228800) ≤ (826020909 / 400000000) := by
  have h := endpoint_bounds (v := ((20089 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_73.1 (by convert! log_c_73.1 using 1; norm_num)
    log_v_73.2 (by convert! log_c_73.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_74 : (821389613 / 200000000) ≤ -Real.log (40447 / 2457600) ∧
    -Real.log (40447 / 2457600) ≤ (4106948071 / 1000000000) := by
  have h := checkLog_sound (w := (36353 / 117247)) (n := 12)
    (lo := (128242433 / 200000000)) (hi := (320606083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 40447) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(76800 / 40447) = 1/(40447 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_74 : (8297431 / 500000000) ≤ -Real.log (2417153 / 2457600) ∧
    -Real.log (2417153 / 2457600) ≤ (16594863 / 1000000000) := by
  have h := checkLog_sound (w := (40447 / 4874753)) (n := 12)
    (lo := (8297431 / 500000000)) (hi := (16594863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2417153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2417153) = 1/(2417153 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_74 : (2045176601 / 1000000000) ≤ xi (40447 / 2457600) ∧ xi (40447 / 2457600) ≤ (4090353209 / 2000000000) ∧
    (4123542927 / 2000000000) ≤ kap (40447 / 2457600) ∧ kap (40447 / 2457600) ≤ (2061771467 / 1000000000) := by
  have h := endpoint_bounds (v := ((40447 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_74.1 (by convert! log_c_74.1 using 1; norm_num)
    log_v_74.2 (by convert! log_c_74.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_75 : (1025079851 / 250000000) ≤ -Real.log (3393 / 204800) ∧
    -Real.log (3393 / 204800) ≤ (410031941 / 100000000) := by
  have h := checkLog_sound (w := (3007 / 9793)) (n := 12)
    (lo := (39661469 / 62500000)) (hi := (126916701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3393) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6400 / 3393) = 1/(3393 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_75 : (4176539 / 250000000) ≤ -Real.log (201407 / 204800) ∧
    -Real.log (201407 / 204800) ≤ (16706157 / 1000000000) := by
  have h := checkLog_sound (w := (3393 / 406207)) (n := 12)
    (lo := (4176539 / 250000000)) (hi := (16706157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 201407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 201407) = 1/(201407 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_75 : (4083613247 / 2000000000) ≤ xi (3393 / 204800) ∧ xi (3393 / 204800) ≤ (2041806627 / 1000000000) ∧
    (102925639 / 50000000) ≤ kap (3393 / 204800) ∧ kap (3393 / 204800) ≤ (4117025567 / 2000000000) := by
  have h := endpoint_bounds (v := ((3393 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_75.1 (by convert! log_c_75.1 using 1; norm_num)
    log_v_75.2 (by convert! log_c_75.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_76 : (2046867197 / 500000000) ≤ -Real.log (8197 / 491520) ∧
    -Real.log (8197 / 491520) ≤ (319823 / 78125) := by
  have h := checkLog_sound (w := (7163 / 23557)) (n := 12)
    (lo := (313999247 / 500000000)) (hi := (125599699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 8197) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15360 / 8197) = 1/(8197 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_76 : (16817463 / 1000000000) ≤ -Real.log (483323 / 491520) ∧
    -Real.log (483323 / 491520) ≤ (2102183 / 125000000) := by
  have h := checkLog_sound (w := (8197 / 974843)) (n := 12)
    (lo := (16817463 / 1000000000)) (hi := (2102183 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491520 / 483323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491520 / 483323) = 1/(483323 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_76 : (407691693 / 200000000) ≤ xi (8197 / 491520) ∧ xi (8197 / 491520) ≤ (4076916937 / 2000000000) ∧
    (4110551857 / 2000000000) ≤ kap (8197 / 491520) ∧ kap (8197 / 491520) ≤ (513818983 / 250000000) := by
  have h := endpoint_bounds (v := ((8197 / 491520) : ℝ)) (by norm_num) (by norm_num)
    log_v_76.1 (by convert! log_c_76.1 using 1; norm_num)
    log_v_76.2 (by convert! log_c_76.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_77 : (2043596231 / 500000000) ≤ -Real.log (20627 / 1228800) ∧
    -Real.log (20627 / 1228800) ≤ (1021798117 / 250000000) := by
  have h := checkLog_sound (w := (17773 / 59027)) (n := 12)
    (lo := (310728281 / 500000000)) (hi := (621456563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 20627) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 20627) = 1/(20627 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_77 : (8464391 / 500000000) ≤ -Real.log (1208173 / 1228800) ∧
    -Real.log (1208173 / 1228800) ≤ (16928783 / 1000000000) := by
  have h := checkLog_sound (w := (20627 / 2436973)) (n := 12)
    (lo := (8464391 / 500000000)) (hi := (16928783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1208173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1208173) = 1/(1208173 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_77 : (4070263679 / 2000000000) ≤ xi (20627 / 1228800) ∧ xi (20627 / 1228800) ≤ (2035131843 / 1000000000) ∧
    (1026030311 / 500000000) ≤ kap (20627 / 1228800) ∧ kap (20627 / 1228800) ≤ (4104121251 / 2000000000) := by
  have h := endpoint_bounds (v := ((20627 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_77.1 (by convert! log_c_77.1 using 1; norm_num)
    log_v_77.2 (by convert! log_c_77.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_78 : (4080693049 / 1000000000) ≤ -Real.log (13841 / 819200) ∧
    -Real.log (13841 / 819200) ≤ (816138611 / 200000000) := by
  have h := checkLog_sound (w := (11759 / 39441)) (n := 12)
    (lo := (614957149 / 1000000000)) (hi := (12299143 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 13841) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25600 / 13841) = 1/(13841 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_78 : (17040113 / 1000000000) ≤ -Real.log (805359 / 819200) ∧
    -Real.log (805359 / 819200) ≤ (8520057 / 500000000) := by
  have h := checkLog_sound (w := (13841 / 1624559)) (n := 12)
    (lo := (17040113 / 1000000000)) (hi := (8520057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 805359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 805359) = 1/(805359 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_78 : (812730587 / 400000000) ≤ xi (13841 / 819200) ∧ xi (13841 / 819200) ≤ (2031826471 / 1000000000) ∧
    (2048866581 / 1000000000) ≤ kap (13841 / 819200) ∧ kap (13841 / 819200) ≤ (4097733169 / 2000000000) := by
  have h := endpoint_bounds (v := ((13841 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_78.1 (by convert! log_c_78.1 using 1; norm_num)
    log_v_78.2 (by convert! log_c_78.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_79 : (2037117803 / 500000000) ≤ -Real.log (653 / 38400) ∧
    -Real.log (653 / 38400) ≤ (1018558903 / 250000000) := by
  have h := checkLog_sound (w := (547 / 1853)) (n := 12)
    (lo := (304249853 / 500000000)) (hi := (608499707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200 / 653) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1200 / 653) = 1/(653 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_79 : (17151457 / 1000000000) ≤ -Real.log (37747 / 38400) ∧
    -Real.log (37747 / 38400) ≤ (8575729 / 500000000) := by
  have h := checkLog_sound (w := (653 / 76147)) (n := 12)
    (lo := (17151457 / 1000000000)) (hi := (8575729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 37747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 37747) = 1/(37747 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_79 : (1014271037 / 500000000) ≤ xi (653 / 38400) ∧ xi (653 / 38400) ≤ (811416831 / 400000000) ∧
    (4091387063 / 2000000000) ≤ kap (653 / 38400) ∧ kap (653 / 38400) ≤ (409138707 / 200000000) := by
  have h := endpoint_bounds (v := ((653 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_79.1 (by convert! log_c_79.1 using 1; norm_num)
    log_v_79.2 (by convert! log_c_79.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


