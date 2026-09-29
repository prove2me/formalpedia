-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs18
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:41:50.771064+00:00
-- url     : https://prove2.me/theorems/77b45e58-91b6-4fc1-b4ea-e09b3d5a102f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs18` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs18` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs18` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs18 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs18.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_288 : (34552107 / 40000000) ≤ -Real.log (64751 / 153600) ∧
    -Real.log (64751 / 153600) ≤ (863802677 / 1000000000) := by
  have h := checkLog_sound (w := (12049 / 141551)) (n := 12)
    (lo := (34131099 / 200000000)) (hi := (21331937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 64751) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 64751) = 1/(64751 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_288 : (547413521 / 1000000000) ≤ -Real.log (88849 / 153600) ∧
    -Real.log (88849 / 153600) ≤ (273706761 / 500000000) := by
  have h := checkLog_sound (w := (64751 / 242449)) (n := 12)
    (lo := (547413521 / 1000000000)) (hi := (273706761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 88849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 88849) = 1/(88849 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_288 : (316389153 / 2000000000) ≤ xi (64751 / 153600) ∧ xi (64751 / 153600) ≤ (79097289 / 500000000) ∧
    (352804049 / 500000000) ≤ kap (64751 / 153600) ∧ kap (64751 / 153600) ≤ (1411216199 / 2000000000) := by
  have h := endpoint_bounds (v := ((64751 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_288.1 (by convert! log_c_288.1 using 1; norm_num)
    log_v_288.2 (by convert! log_c_288.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_289 : (171931381 / 200000000) ≤ -Real.log (3251 / 7680) ∧
    -Real.log (3251 / 7680) ≤ (859656907 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 7091)) (n := 12)
    (lo := (6660389 / 40000000)) (hi := (83254863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 3251) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3840 / 3251) = 1/(3251 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_289 : (275222861 / 500000000) ≤ -Real.log (4429 / 7680) ∧
    -Real.log (4429 / 7680) ≤ (550445723 / 1000000000) := by
  have h := checkLog_sound (w := (3251 / 12109)) (n := 12)
    (lo := (275222861 / 500000000)) (hi := (550445723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 4429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7680 / 4429) = 1/(4429 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_289 : (154605591 / 1000000000) ≤ xi (3251 / 7680) ∧ xi (3251 / 7680) ≤ (61842237 / 400000000) ∧
    (1410102627 / 2000000000) ≤ kap (3251 / 7680) ∧ kap (3251 / 7680) ≤ (141010263 / 200000000) := by
  have h := endpoint_bounds (v := ((3251 / 7680) : ℝ)) (by norm_num) (by norm_num)
    log_v_289.1 (by convert! log_c_289.1 using 1; norm_num)
    log_v_289.2 (by convert! log_c_289.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_290 : (855528251 / 1000000000) ≤ -Real.log (21763 / 51200) ∧
    -Real.log (21763 / 51200) ≤ (855528253 / 1000000000) := by
  have h := checkLog_sound (w := (3837 / 47363)) (n := 12)
    (lo := (162381071 / 1000000000)) (hi := (10148817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 21763) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25600 / 21763) = 1/(21763 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_290 : (110697429 / 200000000) ≤ -Real.log (29437 / 51200) ∧
    -Real.log (29437 / 51200) ≤ (276743573 / 500000000) := by
  have h := checkLog_sound (w := (21763 / 80637)) (n := 12)
    (lo := (110697429 / 200000000)) (hi := (276743573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 29437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 29437) = 1/(29437 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_290 : (60408221 / 400000000) ≤ xi (21763 / 51200) ∧ xi (21763 / 51200) ≤ (75510277 / 500000000) ∧
    (352253849 / 500000000) ≤ kap (21763 / 51200) ∧ kap (21763 / 51200) ≤ (1409015399 / 2000000000) := by
  have h := endpoint_bounds (v := ((21763 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_290.1 (by convert! log_c_290.1 using 1; norm_num)
    log_v_290.2 (by convert! log_c_290.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_291 : (851416573 / 1000000000) ≤ -Real.log (32779 / 76800) ∧
    -Real.log (32779 / 76800) ≤ (34056663 / 40000000) := by
  have h := checkLog_sound (w := (5621 / 71179)) (n := 12)
    (lo := (158269393 / 1000000000)) (hi := (79134697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 32779) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38400 / 32779) = 1/(32779 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_291 : (556537847 / 1000000000) ≤ -Real.log (44021 / 76800) ∧
    -Real.log (44021 / 76800) ≤ (69567231 / 125000000) := by
  have h := checkLog_sound (w := (32779 / 120821)) (n := 12)
    (lo := (556537847 / 1000000000)) (hi := (69567231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 44021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 44021) = 1/(44021 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_291 : (11795149 / 80000000) ≤ xi (32779 / 76800) ∧ xi (32779 / 76800) ≤ (36859841 / 250000000) ∧
    (70397721 / 100000000) ≤ kap (32779 / 76800) ∧ kap (32779 / 76800) ≤ (1407954423 / 2000000000) := by
  have h := endpoint_bounds (v := ((32779 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_291.1 (by convert! log_c_291.1 using 1; norm_num)
    log_v_291.2 (by convert! log_c_291.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_292 : (53085441 / 62500000) ≤ -Real.log (8759 / 20480) ∧
    -Real.log (8759 / 20480) ≤ (424683529 / 500000000) := by
  have h := checkLog_sound (w := (1481 / 18999)) (n := 12)
    (lo := (39054969 / 250000000)) (hi := (156219877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8759) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10240 / 8759) = 1/(8759 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_292 : (111613339 / 200000000) ≤ -Real.log (11721 / 20480) ∧
    -Real.log (11721 / 20480) ≤ (69758337 / 125000000) := by
  have h := checkLog_sound (w := (8759 / 32201)) (n := 12)
    (lo := (111613339 / 200000000)) (hi := (69758337 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 11721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 11721) = 1/(11721 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_292 : (7282509 / 50000000) ≤ xi (8759 / 20480) ∧ xi (8759 / 20480) ≤ (291300363 / 2000000000) ∧
    (1407433751 / 2000000000) ≤ kap (8759 / 20480) ∧ kap (8759 / 20480) ≤ (703716877 / 1000000000) := by
  have h := endpoint_bounds (v := ((8759 / 20480) : ℝ)) (by norm_num) (by norm_num)
    log_v_292.1 (by convert! log_c_292.1 using 1; norm_num)
    log_v_292.2 (by convert! log_c_292.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_293 : (847321731 / 1000000000) ≤ -Real.log (65827 / 153600) ∧
    -Real.log (65827 / 153600) ≤ (847321733 / 1000000000) := by
  have h := checkLog_sound (w := (10973 / 142627)) (n := 12)
    (lo := (154174551 / 1000000000)) (hi := (19271819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 65827) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 65827) = 1/(65827 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_293 : (139899471 / 250000000) ≤ -Real.log (87773 / 153600) ∧
    -Real.log (87773 / 153600) ≤ (111919577 / 200000000) := by
  have h := checkLog_sound (w := (65827 / 241373)) (n := 12)
    (lo := (139899471 / 250000000)) (hi := (111919577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 87773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 87773) = 1/(87773 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_293 : (143861923 / 1000000000) ≤ xi (65827 / 153600) ∧ xi (65827 / 153600) ≤ (287723849 / 2000000000) ∧
    (281383923 / 400000000) ≤ kap (65827 / 153600) ∧ kap (65827 / 153600) ≤ (703459809 / 1000000000) := by
  have h := endpoint_bounds (v := ((65827 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_293.1 (by convert! log_c_293.1 using 1; norm_num)
    log_v_293.2 (by convert! log_c_293.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_294 : (845280581 / 1000000000) ≤ -Real.log (131923 / 307200) ∧
    -Real.log (131923 / 307200) ≤ (845280583 / 1000000000) := by
  have h := checkLog_sound (w := (21677 / 285523)) (n := 12)
    (lo := (152133401 / 1000000000)) (hi := (76066701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 131923) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 131923) = 1/(131923 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_294 : (561131421 / 1000000000) ≤ -Real.log (175277 / 307200) ∧
    -Real.log (175277 / 307200) ≤ (280565711 / 500000000) := by
  have h := checkLog_sound (w := (131923 / 482477)) (n := 12)
    (lo := (561131421 / 1000000000)) (hi := (280565711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 175277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 175277) = 1/(175277 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_294 : (284149159 / 2000000000) ≤ xi (131923 / 307200) ∧ xi (131923 / 307200) ≤ (142074581 / 1000000000) ∧
    (703206001 / 1000000000) ≤ kap (131923 / 307200) ∧ kap (131923 / 307200) ≤ (281282401 / 400000000) := by
  have h := endpoint_bounds (v := ((131923 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_294.1 (by convert! log_c_294.1 using 1; norm_num)
    log_v_294.2 (by convert! log_c_294.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_295 : (843243589 / 1000000000) ≤ -Real.log (1377 / 3200) ∧
    -Real.log (1377 / 3200) ≤ (843243591 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1377) = 1/(1377 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_295 : (281333657 / 500000000) ≤ -Real.log (1823 / 3200) ∧
    -Real.log (1823 / 3200) ≤ (112533463 / 200000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3200 / 1823) = 1/(1823 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_295 : (140288137 / 1000000000) ≤ xi (1377 / 3200) ∧ xi (1377 / 3200) ≤ (280576277 / 2000000000) ∧
    (1405910903 / 2000000000) ≤ kap (1377 / 3200) ∧ kap (1377 / 3200) ≤ (702955453 / 1000000000) := by
  have h := endpoint_bounds (v := ((1377 / 3200) : ℝ)) (by norm_num) (by norm_num)
    log_v_295.1 (by convert! log_c_295.1 using 1; norm_num)
    log_v_295.2 (by convert! log_c_295.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_296 : (420605369 / 500000000) ≤ -Real.log (132461 / 307200) ∧
    -Real.log (132461 / 307200) ≤ (42060537 / 50000000) := by
  have h := checkLog_sound (w := (21139 / 286061)) (n := 12)
    (lo := (74031779 / 500000000)) (hi := (148063559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 132461) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 132461) = 1/(132461 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_296 : (564205569 / 1000000000) ≤ -Real.log (174739 / 307200) ∧
    -Real.log (174739 / 307200) ≤ (56420557 / 100000000) := by
  have h := checkLog_sound (w := (132461 / 481939)) (n := 12)
    (lo := (564205569 / 1000000000)) (hi := (56420557 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 174739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 174739) = 1/(174739 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_296 : (17312823 / 125000000) ≤ xi (132461 / 307200) ∧ xi (132461 / 307200) ≤ (277005171 / 2000000000) ∧
    (1405416307 / 2000000000) ≤ kap (132461 / 307200) ∧ kap (132461 / 307200) ≤ (140541631 / 200000000) := by
  have h := endpoint_bounds (v := ((132461 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_296.1 (by convert! log_c_296.1 using 1; norm_num)
    log_v_296.2 (by convert! log_c_296.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_297 : (839182011 / 1000000000) ≤ -Real.log (13273 / 30720) ∧
    -Real.log (13273 / 30720) ≤ (839182013 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 28633)) (n := 12)
    (lo := (146034831 / 1000000000)) (hi := (9127177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 13273) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15360 / 13273) = 1/(13273 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_297 : (282873097 / 500000000) ≤ -Real.log (17447 / 30720) ∧
    -Real.log (17447 / 30720) ≤ (113149239 / 200000000) := by
  have h := checkLog_sound (w := (13273 / 48167)) (n := 12)
    (lo := (282873097 / 500000000)) (hi := (113149239 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30720 / 17447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30720 / 17447) = 1/(17447 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_297 : (34179477 / 250000000) ≤ xi (13273 / 30720) ∧ xi (13273 / 30720) ≤ (273435819 / 2000000000) ∧
    (280985641 / 400000000) ≤ kap (13273 / 30720) ∧ kap (13273 / 30720) ≤ (87808013 / 125000000) := by
  have h := endpoint_bounds (v := ((13273 / 30720) : ℝ)) (by norm_num) (by norm_num)
    log_v_297.1 (by convert! log_c_297.1 using 1; norm_num)
    log_v_297.2 (by convert! log_c_297.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_298 : (837157391 / 1000000000) ≤ -Real.log (44333 / 102400) ∧
    -Real.log (44333 / 102400) ≤ (837157393 / 1000000000) := by
  have h := checkLog_sound (w := (6867 / 95533)) (n := 12)
    (lo := (144010211 / 1000000000)) (hi := (36002553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 44333) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51200 / 44333) = 1/(44333 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_298 : (141822299 / 250000000) ≤ -Real.log (58067 / 102400) ∧
    -Real.log (58067 / 102400) ≤ (567289197 / 1000000000) := by
  have h := checkLog_sound (w := (44333 / 160467)) (n := 12)
    (lo := (141822299 / 250000000)) (hi := (567289197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 58067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 58067) = 1/(58067 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_298 : (134934097 / 1000000000) ≤ xi (44333 / 102400) ∧ xi (44333 / 102400) ≤ (269868197 / 2000000000) ∧
    (1404446587 / 2000000000) ≤ kap (44333 / 102400) ∧ kap (44333 / 102400) ≤ (140444659 / 200000000) := by
  have h := endpoint_bounds (v := ((44333 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_298.1 (by convert! log_c_298.1 using 1; norm_num)
    log_v_298.2 (by convert! log_c_298.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_299 : (417568431 / 500000000) ≤ -Real.log (33317 / 76800) ∧
    -Real.log (33317 / 76800) ≤ (26098027 / 31250000) := by
  have h := checkLog_sound (w := (5083 / 71717)) (n := 12)
    (lo := (70994841 / 500000000)) (hi := (141989683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 33317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38400 / 33317) = 1/(33317 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_299 : (568834583 / 1000000000) ≤ -Real.log (43483 / 76800) ∧
    -Real.log (43483 / 76800) ≤ (71104323 / 125000000) := by
  have h := checkLog_sound (w := (33317 / 120283)) (n := 12)
    (lo := (568834583 / 1000000000)) (hi := (71104323 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 43483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 43483) = 1/(43483 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_299 : (133151139 / 1000000000) ≤ xi (33317 / 76800) ∧ xi (33317 / 76800) ≤ (266302281 / 2000000000) ∧
    (280794289 / 400000000) ≤ kap (33317 / 76800) ∧ kap (33317 / 76800) ≤ (175496431 / 250000000) := by
  have h := endpoint_bounds (v := ((33317 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_299.1 (by convert! log_c_299.1 using 1; norm_num)
    log_v_299.2 (by convert! log_c_299.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_300 : (833120407 / 1000000000) ≤ -Real.log (133537 / 307200) ∧
    -Real.log (133537 / 307200) ≤ (833120409 / 1000000000) := by
  have h := checkLog_sound (w := (20063 / 287137)) (n := 12)
    (lo := (139973227 / 1000000000)) (hi := (34993307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 133537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 133537) = 1/(133537 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_300 : (570382361 / 1000000000) ≤ -Real.log (173663 / 307200) ∧
    -Real.log (173663 / 307200) ≤ (285191181 / 500000000) := by
  have h := checkLog_sound (w := (133537 / 480863)) (n := 12)
    (lo := (570382361 / 1000000000)) (hi := (285191181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 173663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 173663) = 1/(173663 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_300 : (52547609 / 400000000) ≤ xi (133537 / 307200) ∧ xi (133537 / 307200) ≤ (2052641 / 15625000) ∧
    (87718923 / 125000000) ≤ kap (133537 / 307200) ∧ kap (133537 / 307200) ≤ (1403502771 / 2000000000) := by
  have h := endpoint_bounds (v := ((133537 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_300.1 (by convert! log_c_300.1 using 1; norm_num)
    log_v_300.2 (by convert! log_c_300.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_301 : (83110801 / 100000000) ≤ -Real.log (22301 / 51200) ∧
    -Real.log (22301 / 51200) ≤ (207777003 / 250000000) := by
  have h := checkLog_sound (w := (3299 / 47901)) (n := 12)
    (lo := (13796083 / 100000000)) (hi := (137960831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 22301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25600 / 22301) = 1/(22301 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_301 : (571932539 / 1000000000) ≤ -Real.log (28899 / 51200) ∧
    -Real.log (28899 / 51200) ≤ (28596627 / 50000000) := by
  have h := checkLog_sound (w := (22301 / 80099)) (n := 12)
    (lo := (571932539 / 1000000000)) (hi := (28596627 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 28899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 28899) = 1/(28899 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_301 : (25917547 / 200000000) ≤ xi (22301 / 51200) ∧ xi (22301 / 51200) ≤ (259175473 / 2000000000) ∧
    (1403040549 / 2000000000) ≤ kap (22301 / 51200) ∧ kap (22301 / 51200) ≤ (175380069 / 250000000) := by
  have h := endpoint_bounds (v := ((22301 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_301.1 (by convert! log_c_301.1 using 1; norm_num)
    log_v_301.2 (by convert! log_c_301.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_302 : (165819931 / 200000000) ≤ -Real.log (5363 / 12288) ∧
    -Real.log (5363 / 12288) ≤ (829099657 / 1000000000) := by
  have h := checkLog_sound (w := (781 / 11507)) (n := 12)
    (lo := (5438099 / 40000000)) (hi := (33988119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6144 / 5363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6144 / 5363) = 1/(5363 / 12288) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_302 : (143371281 / 250000000) ≤ -Real.log (6925 / 12288) ∧
    -Real.log (6925 / 12288) ≤ (4587881 / 8000000) := by
  have h := checkLog_sound (w := (5363 / 19213)) (n := 12)
    (lo := (143371281 / 250000000)) (hi := (4587881 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12288 / 6925) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12288 / 6925) = 1/(6925 / 12288) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_302 : (25561453 / 200000000) ≤ xi (5363 / 12288) ∧ xi (5363 / 12288) ≤ (255614533 / 2000000000) ∧
    (1402584779 / 2000000000) ≤ kap (5363 / 12288) ∧ kap (5363 / 12288) ≤ (701292391 / 1000000000) := by
  have h := endpoint_bounds (v := ((5363 / 12288) : ℝ)) (by norm_num) (by norm_num)
    log_v_302.1 (by convert! log_c_302.1 using 1; norm_num)
    log_v_302.2 (by convert! log_c_302.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_303 : (413547663 / 500000000) ≤ -Real.log (16793 / 38400) ∧
    -Real.log (16793 / 38400) ≤ (25846729 / 31250000) := by
  have h := checkLog_sound (w := (2407 / 35993)) (n := 12)
    (lo := (66974073 / 500000000)) (hi := (133948147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 16793) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 16793) = 1/(16793 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_303 : (575040123 / 1000000000) ≤ -Real.log (21607 / 38400) ∧
    -Real.log (21607 / 38400) ≤ (143760031 / 250000000) := by
  have h := checkLog_sound (w := (16793 / 60007)) (n := 12)
    (lo := (575040123 / 1000000000)) (hi := (143760031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 21607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 21607) = 1/(21607 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_303 : (126027601 / 1000000000) ≤ xi (16793 / 38400) ∧ xi (16793 / 38400) ≤ (50411041 / 400000000) ∧
    (1402135449 / 2000000000) ≤ kap (16793 / 38400) ∧ kap (16793 / 38400) ≤ (350533863 / 500000000) := by
  have h := endpoint_bounds (v := ((16793 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_303.1 (by convert! log_c_303.1 using 1; norm_num)
    log_v_303.2 (by convert! log_c_303.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


