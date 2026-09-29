-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs09
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:44:21.407757+00:00
-- url     : https://prove2.me/theorems/6fd929e2-6144-464a-b281-e2c4970c34ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs09` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs09` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs09` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs09 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs09.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_144 : (341833559 / 100000000) ≤ -Real.log (5033 / 153600) ∧
    -Real.log (5033 / 153600) ≤ (683667119 / 200000000) := by
  have h := checkLog_sound (w := (4567 / 14633)) (n := 12)
    (lo := (64574687 / 100000000)) (hi := (645746871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 5033) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9600 / 5033) = 1/(5033 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_144 : (6663157 / 200000000) ≤ -Real.log (148567 / 153600) ∧
    -Real.log (148567 / 153600) ≤ (16657893 / 500000000) := by
  have h := checkLog_sound (w := (5033 / 302167)) (n := 12)
    (lo := (6663157 / 200000000)) (hi := (16657893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 148567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 148567) = 1/(148567 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_144 : (846254951 / 500000000) ≤ xi (5033 / 153600) ∧ xi (5033 / 153600) ≤ (338501981 / 200000000) ∧
    (27613211 / 16000000) ≤ kap (5033 / 153600) ∧ kap (5033 / 153600) ≤ (3451651381 / 2000000000) := by
  have h := endpoint_bounds (v := ((5033 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_144.1 (by convert! log_c_144.1 using 1; norm_num)
    log_v_144.2 (by convert! log_c_144.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_145 : (170253113 / 50000000) ≤ -Real.log (20401 / 614400) ∧
    -Real.log (20401 / 614400) ≤ (681012453 / 200000000) := by
  have h := checkLog_sound (w := (17999 / 58801)) (n := 12)
    (lo := (31623677 / 50000000)) (hi := (632473541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 20401) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 20401) = 1/(20401 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_145 : (6753709 / 200000000) ≤ -Real.log (593999 / 614400) ∧
    -Real.log (593999 / 614400) ≤ (16884273 / 500000000) := by
  have h := checkLog_sound (w := (20401 / 1208399)) (n := 12)
    (lo := (6753709 / 200000000)) (hi := (16884273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 593999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 593999) = 1/(593999 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_145 : (1685646857 / 1000000000) ≤ xi (20401 / 614400) ∧ xi (20401 / 614400) ≤ (84282343 / 50000000) ∧
    (687766161 / 400000000) ≤ kap (20401 / 614400) ∧ kap (20401 / 614400) ≤ (3438830811 / 2000000000) := by
  have h := endpoint_bounds (v := ((20401 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_145.1 (by convert! log_c_145.1 using 1; norm_num)
    log_v_145.2 (by convert! log_c_145.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_146 : (678392561 / 200000000) ≤ -Real.log (689 / 20480) ∧
    -Real.log (689 / 20480) ≤ (339196281 / 100000000) := by
  have h := checkLog_sound (w := (591 / 1969)) (n := 12)
    (lo := (123874817 / 200000000)) (hi := (309687043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 689) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 689) = 1/(689 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_146 : (34221511 / 1000000000) ≤ -Real.log (19791 / 20480) ∧
    -Real.log (19791 / 20480) ≤ (4277689 / 125000000) := by
  have h := checkLog_sound (w := (689 / 40271)) (n := 12)
    (lo := (34221511 / 1000000000)) (hi := (4277689 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 19791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 19791) = 1/(19791 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_146 : (3357741293 / 2000000000) ≤ xi (689 / 20480) ∧ xi (689 / 20480) ≤ (3357741299 / 2000000000) ∧
    (856546079 / 500000000) ≤ kap (689 / 20480) ∧ kap (689 / 20480) ≤ (1713092161 / 1000000000) := by
  have h := endpoint_bounds (v := ((689 / 20480) : ℝ)) (by norm_num) (by norm_num)
    log_v_146.1 (by convert! log_c_146.1 using 1; norm_num)
    log_v_146.2 (by convert! log_c_146.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_147 : (337903273 / 100000000) ≤ -Real.log (20939 / 614400) ∧
    -Real.log (20939 / 614400) ≤ (675806547 / 200000000) := by
  have h := checkLog_sound (w := (17461 / 59339)) (n := 12)
    (lo := (60644401 / 100000000)) (hi := (606444011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 20939) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 20939) = 1/(20939 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_147 : (34674681 / 1000000000) ≤ -Real.log (593461 / 614400) ∧
    -Real.log (593461 / 614400) ≤ (17337341 / 500000000) := by
  have h := checkLog_sound (w := (20939 / 1207861)) (n := 12)
    (lo := (34674681 / 1000000000)) (hi := (17337341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 593461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 593461) = 1/(593461 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_147 : (104511189 / 62500000) ≤ xi (20939 / 614400) ∧ xi (20939 / 614400) ≤ (1672179027 / 1000000000) ∧
    (3413707411 / 2000000000) ≤ kap (20939 / 614400) ∧ kap (20939 / 614400) ≤ (3413707417 / 2000000000) := by
  have h := endpoint_bounds (v := ((20939 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_147.1 (by convert! log_c_147.1 using 1; norm_num)
    log_v_147.2 (by convert! log_c_147.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_148 : (336626771 / 100000000) ≤ -Real.log (2651 / 76800) ∧
    -Real.log (2651 / 76800) ≤ (673253543 / 200000000) := by
  have h := checkLog_sound (w := (2149 / 7451)) (n := 12)
    (lo := (59367899 / 100000000)) (hi := (593678991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 2651) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4800 / 2651) = 1/(2651 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_148 : (35128057 / 1000000000) ≤ -Real.log (74149 / 76800) ∧
    -Real.log (74149 / 76800) ≤ (17564029 / 500000000) := by
  have h := checkLog_sound (w := (2651 / 150949)) (n := 12)
    (lo := (35128057 / 1000000000)) (hi := (17564029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 74149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 74149) = 1/(74149 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_148 : (832784913 / 500000000) ≤ xi (2651 / 76800) ∧ xi (2651 / 76800) ≤ (1665569829 / 1000000000) ∧
    (3401395767 / 2000000000) ≤ kap (2651 / 76800) ∧ kap (2651 / 76800) ≤ (3401395773 / 2000000000) := by
  have h := endpoint_bounds (v := ((2651 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_148.1 (by convert! log_c_148.1 using 1; norm_num)
    log_v_148.2 (by convert! log_c_148.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_149 : (104801987 / 31250000) ≤ -Real.log (7159 / 204800) ∧
    -Real.log (7159 / 204800) ≤ (3353663589 / 1000000000) := by
  have h := checkLog_sound (w := (5641 / 19959)) (n := 12)
    (lo := (36317179 / 62500000)) (hi := (116214973 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 7159) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12800 / 7159) = 1/(7159 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_149 : (35581639 / 1000000000) ≤ -Real.log (197641 / 204800) ∧
    -Real.log (197641 / 204800) ≤ (889541 / 25000000) := by
  have h := checkLog_sound (w := (7159 / 402441)) (n := 12)
    (lo := (35581639 / 1000000000)) (hi := (889541 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 197641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 197641) = 1/(197641 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_149 : (414760243 / 250000000) ≤ xi (7159 / 204800) ∧ xi (7159 / 204800) ≤ (66361639 / 40000000) ∧
    (3389245223 / 2000000000) ≤ kap (7159 / 204800) ∧ kap (7159 / 204800) ≤ (3389245229 / 2000000000) := by
  have h := endpoint_bounds (v := ((7159 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_149.1 (by convert! log_c_149.1 using 1; norm_num)
    log_v_149.2 (by convert! log_c_149.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_150 : (3341216347 / 1000000000) ≤ -Real.log (10873 / 307200) ∧
    -Real.log (10873 / 307200) ≤ (104413011 / 31250000) := by
  have h := checkLog_sound (w := (8327 / 30073)) (n := 12)
    (lo := (568627627 / 1000000000)) (hi := (142156907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 10873) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 10873) = 1/(10873 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_150 : (18017713 / 500000000) ≤ -Real.log (296327 / 307200) ∧
    -Real.log (296327 / 307200) ≤ (36035427 / 1000000000) := by
  have h := checkLog_sound (w := (10873 / 603527)) (n := 12)
    (lo := (18017713 / 500000000)) (hi := (36035427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 296327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 296327) = 1/(296327 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_150 : (82629523 / 50000000) ≤ xi (10873 / 307200) ∧ xi (10873 / 307200) ≤ (1652590463 / 1000000000) ∧
    (3377251773 / 2000000000) ≤ kap (10873 / 307200) ∧ kap (10873 / 307200) ≤ (3377251779 / 2000000000) := by
  have h := endpoint_bounds (v := ((10873 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_150.1 (by convert! log_c_150.1 using 1; norm_num)
    log_v_150.2 (by convert! log_c_150.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_151 : (166446107 / 50000000) ≤ -Real.log (4403 / 122880) ∧
    -Real.log (4403 / 122880) ≤ (665784429 / 200000000) := by
  have h := checkLog_sound (w := (3277 / 12083)) (n := 12)
    (lo := (27816671 / 50000000)) (hi := (556333421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 4403) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7680 / 4403) = 1/(4403 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_151 : (1824471 / 50000000) ≤ -Real.log (118477 / 122880) ∧
    -Real.log (118477 / 122880) ≤ (36489421 / 1000000000) := by
  have h := checkLog_sound (w := (4403 / 241357)) (n := 12)
    (lo := (1824471 / 50000000)) (hi := (36489421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122880 / 118477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122880 / 118477) = 1/(118477 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_151 : (3292432719 / 2000000000) ≤ xi (4403 / 122880) ∧ xi (4403 / 122880) ≤ (131697309 / 80000000) ∧
    (84135289 / 50000000) ≤ kap (4403 / 122880) ∧ kap (4403 / 122880) ≤ (1682705783 / 1000000000) := by
  have h := endpoint_bounds (v := ((4403 / 122880) : ℝ)) (by norm_num) (by norm_num)
    log_v_151.1 (by convert! log_c_151.1 using 1; norm_num)
    log_v_151.2 (by convert! log_c_151.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_152 : (3316777247 / 1000000000) ≤ -Real.log (1857 / 51200) ∧
    -Real.log (1857 / 51200) ≤ (829194313 / 250000000) := by
  have h := checkLog_sound (w := (1343 / 5057)) (n := 12)
    (lo := (544188527 / 1000000000)) (hi := (34011783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1857) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1857) = 1/(1857 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_152 : (1847181 / 50000000) ≤ -Real.log (49343 / 51200) ∧
    -Real.log (49343 / 51200) ≤ (36943621 / 1000000000) := by
  have h := checkLog_sound (w := (1857 / 100543)) (n := 12)
    (lo := (1847181 / 50000000)) (hi := (36943621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 49343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 49343) = 1/(49343 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_152 : (1639916813 / 1000000000) ≤ xi (1857 / 51200) ∧ xi (1857 / 51200) ≤ (102494801 / 62500000) ∧
    (3353720867 / 2000000000) ≤ kap (1857 / 51200) ∧ kap (1857 / 51200) ≤ (3353720873 / 2000000000) := by
  have h := endpoint_bounds (v := ((1857 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_152.1 (by convert! log_c_152.1 using 1; norm_num)
    log_v_152.2 (by convert! log_c_152.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_153 : (826194521 / 250000000) ≤ -Real.log (22553 / 614400) ∧
    -Real.log (22553 / 614400) ≤ (3304778089 / 1000000000) := by
  have h := checkLog_sound (w := (15847 / 60953)) (n := 12)
    (lo := (133047341 / 250000000)) (hi := (106437873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 22553) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 22553) = 1/(22553 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_153 : (18699013 / 500000000) ≤ -Real.log (591847 / 614400) ∧
    -Real.log (591847 / 614400) ≤ (37398027 / 1000000000) := by
  have h := checkLog_sound (w := (22553 / 1206247)) (n := 12)
    (lo := (18699013 / 500000000)) (hi := (37398027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 591847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 591847) = 1/(591847 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_153 : (3267380057 / 2000000000) ≤ xi (22553 / 614400) ∧ xi (22553 / 614400) ≤ (3267380063 / 2000000000) ∧
    (334217611 / 200000000) ≤ kap (22553 / 614400) ∧ kap (22553 / 614400) ≤ (835544029 / 500000000) := by
  have h := endpoint_bounds (v := ((22553 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_153.1 (by convert! log_c_153.1 using 1; norm_num)
    log_v_153.2 (by convert! log_c_153.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_154 : (823230299 / 250000000) ≤ -Real.log (11411 / 307200) ∧
    -Real.log (11411 / 307200) ≤ (3292921201 / 1000000000) := by
  have h := checkLog_sound (w := (7789 / 30611)) (n := 12)
    (lo := (130083119 / 250000000)) (hi := (520332477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 11411) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 11411) = 1/(11411 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_154 : (18926319 / 500000000) ≤ -Real.log (295789 / 307200) ∧
    -Real.log (295789 / 307200) ≤ (37852639 / 1000000000) := by
  have h := checkLog_sound (w := (11411 / 602989)) (n := 12)
    (lo := (18926319 / 500000000)) (hi := (37852639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 295789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 295789) = 1/(295789 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_154 : (3255068557 / 2000000000) ≤ xi (11411 / 307200) ∧ xi (11411 / 307200) ≤ (3255068563 / 2000000000) ∧
    (1665386917 / 1000000000) ≤ kap (11411 / 307200) ∧ kap (11411 / 307200) ≤ (41634673 / 25000000) := by
  have h := endpoint_bounds (v := ((11411 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_154.1 (by convert! log_c_154.1 using 1; norm_num)
    log_v_154.2 (by convert! log_c_154.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_155 : (205075203 / 62500000) ≤ -Real.log (7697 / 204800) ∧
    -Real.log (7697 / 204800) ≤ (3281203253 / 1000000000) := by
  have h := checkLog_sound (w := (5103 / 20497)) (n := 12)
    (lo := (3973551 / 7812500)) (hi := (508614529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 7697) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12800 / 7697) = 1/(7697 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_155 : (19153729 / 500000000) ≤ -Real.log (197103 / 204800) ∧
    -Real.log (197103 / 204800) ≤ (38307459 / 1000000000) := by
  have h := checkLog_sound (w := (7697 / 401903)) (n := 12)
    (lo := (19153729 / 500000000)) (hi := (38307459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 197103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 197103) = 1/(197103 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_155 : (3242895789 / 2000000000) ≤ xi (7697 / 204800) ∧ xi (7697 / 204800) ≤ (648579159 / 400000000) ∧
    (1659755353 / 1000000000) ≤ kap (7697 / 204800) ∧ kap (7697 / 204800) ≤ (414938839 / 250000000) := by
  have h := endpoint_bounds (v := ((7697 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_155.1 (by convert! log_c_155.1 using 1; norm_num)
    log_v_155.2 (by convert! log_c_155.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_156 : (3269621021 / 1000000000) ≤ -Real.log (73 / 1920) ∧
    -Real.log (73 / 1920) ≤ (1634810513 / 500000000) := by
  have h := checkLog_sound (w := (47 / 193)) (n := 12)
    (lo := (497032301 / 1000000000)) (hi := (248516151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120 / 73) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(120 / 73) = 1/(73 / 1920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_156 : (9690621 / 250000000) ≤ -Real.log (1847 / 1920) ∧
    -Real.log (1847 / 1920) ≤ (7752497 / 200000000) := by
  have h := checkLog_sound (w := (73 / 3767)) (n := 12)
    (lo := (9690621 / 250000000)) (hi := (7752497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920 / 1847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1920 / 1847) = 1/(1847 / 1920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_156 : (403857317 / 250000000) ≤ xi (73 / 1920) ∧ xi (73 / 1920) ≤ (1615429271 / 1000000000) ∧
    (661676701 / 400000000) ≤ kap (73 / 1920) ∧ kap (73 / 1920) ≤ (3308383511 / 2000000000) := by
  have h := endpoint_bounds (v := ((73 / 1920) : ℝ)) (by norm_num) (by norm_num)
    log_v_156.1 (by convert! log_c_156.1 using 1; norm_num)
    log_v_156.2 (by convert! log_c_156.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_157 : (203635713 / 62500000) ≤ -Real.log (23629 / 614400) ∧
    -Real.log (23629 / 614400) ≤ (3258171413 / 1000000000) := by
  have h := checkLog_sound (w := (14771 / 62029)) (n := 12)
    (lo := (15174459 / 31250000)) (hi := (485582689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 23629) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 23629) = 1/(23629 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_157 : (19608859 / 500000000) ≤ -Real.log (590771 / 614400) ∧
    -Real.log (590771 / 614400) ≤ (39217719 / 1000000000) := by
  have h := checkLog_sound (w := (23629 / 1205171)) (n := 12)
    (lo := (19608859 / 500000000)) (hi := (39217719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 590771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 590771) = 1/(590771 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_157 : (3218953689 / 2000000000) ≤ xi (23629 / 614400) ∧ xi (23629 / 614400) ≤ (643790739 / 400000000) ∧
    (1648694563 / 1000000000) ≤ kap (23629 / 614400) ∧ kap (23629 / 614400) ≤ (824347283 / 500000000) := by
  have h := endpoint_bounds (v := ((23629 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_157.1 (by convert! log_c_157.1 using 1; norm_num)
    log_v_157.2 (by convert! log_c_157.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_158 : (1623425703 / 500000000) ≤ -Real.log (3983 / 102400) ∧
    -Real.log (3983 / 102400) ≤ (3246851411 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 10383)) (n := 12)
    (lo := (237131343 / 500000000)) (hi := (474262687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3983) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 3983) = 1/(3983 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_158 : (39673159 / 1000000000) ≤ -Real.log (98417 / 102400) ∧
    -Real.log (98417 / 102400) ≤ (991829 / 25000000) := by
  have h := checkLog_sound (w := (3983 / 200817)) (n := 12)
    (lo := (39673159 / 1000000000)) (hi := (991829 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 98417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 98417) = 1/(98417 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_158 : (1603589123 / 1000000000) ≤ xi (3983 / 102400) ∧ xi (3983 / 102400) ≤ (801794563 / 500000000) ∧
    (657304913 / 400000000) ≤ kap (3983 / 102400) ∧ kap (3983 / 102400) ≤ (3286524571 / 2000000000) := by
  have h := endpoint_bounds (v := ((3983 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_158.1 (by convert! log_c_158.1 using 1; norm_num)
    log_v_158.2 (by convert! log_c_158.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_159 : (3235658113 / 1000000000) ≤ -Real.log (24167 / 614400) ∧
    -Real.log (24167 / 614400) ≤ (1617829059 / 500000000) := by
  have h := checkLog_sound (w := (14233 / 62567)) (n := 12)
    (lo := (463069393 / 1000000000)) (hi := (231534697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 24167) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 24167) = 1/(24167 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_159 : (40128807 / 1000000000) ≤ -Real.log (590233 / 614400) ∧
    -Real.log (590233 / 614400) ≤ (5016101 / 125000000) := by
  have h := checkLog_sound (w := (24167 / 1204633)) (n := 12)
    (lo := (40128807 / 1000000000)) (hi := (5016101 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 590233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 590233) = 1/(590233 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_159 : (639105861 / 400000000) ≤ xi (24167 / 614400) ∧ xi (24167 / 614400) ≤ (3195529311 / 2000000000) ∧
    (81894673 / 50000000) ≤ kap (24167 / 614400) ∧ kap (24167 / 614400) ≤ (1637893463 / 1000000000) := by
  have h := endpoint_bounds (v := ((24167 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_159.1 (by convert! log_c_159.1 using 1; norm_num)
    log_v_159.2 (by convert! log_c_159.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


