-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs00
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:49:13.154631+00:00
-- url     : https://prove2.me/theorems/b9dd697e-586f-48b3-8022-4c6608aa007b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs00` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs00` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs00` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs00 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs00.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_0 : (2302585091 / 500000000) ≤ -Real.log (1 / 100) ∧
    -Real.log (1 / 100) ≤ (4605170189 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25 / 16) = 1/(1 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_0 : (2010067 / 200000000) ≤ -Real.log (99 / 100) ∧
    -Real.log (99 / 100) ≤ (314073 / 31250000) := by
  have h := checkLog_sound (w := (1 / 199)) (n := 12)
    (lo := (2010067 / 200000000)) (hi := (314073 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 99) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 99) = 1/(99 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_0 : (2297559923 / 1000000000) ≤ xi (1 / 100) ∧ xi (1 / 100) ≤ (2297559927 / 1000000000) ∧
    (4615220517 / 2000000000) ≤ kap (1 / 100) ∧ kap (1 / 100) ≤ (184608821 / 80000000) := by
  have h := endpoint_bounds (v := ((1 / 100) : ℝ)) (by norm_num) (by norm_num)
    log_v_0.1 (by convert! log_c_0.1 using 1; norm_num)
    log_v_0.2 (by convert! log_c_0.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_1 : (919942457 / 200000000) ≤ -Real.log (49421 / 4915200) ∧
    -Real.log (49421 / 4915200) ≤ (1149928073 / 250000000) := by
  have h := checkLog_sound (w := (27379 / 126221)) (n := 12)
    (lo := (88165841 / 200000000)) (hi := (220414603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 49421) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 49421) = 1/(49421 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_1 : (5052809 / 500000000) ≤ -Real.log (4865779 / 4915200) ∧
    -Real.log (4865779 / 4915200) ≤ (10105619 / 1000000000) := by
  have h := checkLog_sound (w := (49421 / 9780979)) (n := 12)
    (lo := (5052809 / 500000000)) (hi := (10105619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4865779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4865779) = 1/(4865779 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_1 : (2294803333 / 1000000000) ≤ xi (49421 / 4915200) ∧ xi (49421 / 4915200) ≤ (2294803337 / 1000000000) ∧
    (4609817903 / 2000000000) ≤ kap (49421 / 4915200) ∧ kap (49421 / 4915200) ≤ (4609817911 / 2000000000) := by
  have h := endpoint_bounds (v := ((49421 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_1.1 (by convert! log_c_1.1 using 1; norm_num)
    log_v_1.2 (by convert! log_c_1.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_2 : (2297142007 / 500000000) ≤ -Real.log (4969 / 491520) ∧
    -Real.log (4969 / 491520) ≤ (4594284021 / 1000000000) := by
  have h := checkLog_sound (w := (2711 / 12649)) (n := 12)
    (lo := (217700467 / 500000000)) (hi := (87080187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 4969) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7680 / 4969) = 1/(4969 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_2 : (10160903 / 1000000000) ≤ -Real.log (486551 / 491520) ∧
    -Real.log (486551 / 491520) ≤ (1270113 / 125000000) := by
  have h := checkLog_sound (w := (4969 / 978071)) (n := 12)
    (lo := (10160903 / 1000000000)) (hi := (1270113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491520 / 486551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491520 / 486551) = 1/(486551 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_2 : (458412311 / 200000000) ≤ xi (4969 / 491520) ∧ xi (4969 / 491520) ≤ (2292061559 / 1000000000) ∧
    (4604444917 / 2000000000) ≤ kap (4969 / 491520) ∧ kap (4969 / 491520) ≤ (184177797 / 80000000) := by
  have h := endpoint_bounds (v := ((4969 / 491520) : ℝ)) (by norm_num) (by norm_num)
    log_v_2.1 (by convert! log_c_2.1 using 1; norm_num)
    log_v_2.2 (by convert! log_c_2.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_3 : (4588885051 / 1000000000) ≤ -Real.log (16653 / 1638400) ∧
    -Real.log (16653 / 1638400) ≤ (2294442529 / 500000000) := by
  have h := checkLog_sound (w := (8947 / 42253)) (n := 12)
    (lo := (430001971 / 1000000000)) (hi := (107500493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 16653) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25600 / 16653) = 1/(16653 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_3 : (39907 / 3906250) ≤ -Real.log (1621747 / 1638400) ∧
    -Real.log (1621747 / 1638400) ≤ (10216193 / 1000000000) := by
  have h := checkLog_sound (w := (16653 / 3260147)) (n := 12)
    (lo := (39907 / 3906250)) (hi := (10216193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638400 / 1621747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638400 / 1621747) = 1/(1621747 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_3 : (2289334429 / 1000000000) ≤ xi (16653 / 1638400) ∧ xi (16653 / 1638400) ≤ (2289334433 / 1000000000) ∧
    (4599101243 / 2000000000) ≤ kap (16653 / 1638400) ∧ kap (16653 / 1638400) ≤ (4599101251 / 2000000000) := by
  have h := endpoint_bounds (v := ((16653 / 1638400) : ℝ)) (by norm_num) (by norm_num)
    log_v_3.1 (by convert! log_c_3.1 using 1; norm_num)
    log_v_3.2 (by convert! log_c_3.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_4 : (114587877 / 25000000) ≤ -Real.log (12557 / 1228800) ∧
    -Real.log (12557 / 1228800) ≤ (4583515087 / 1000000000) := by
  have h := checkLog_sound (w := (6643 / 31757)) (n := 12)
    (lo := (53079 / 125000)) (hi := (424632001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 12557) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19200 / 12557) = 1/(12557 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_4 : (2567871 / 250000000) ≤ -Real.log (1216243 / 1228800) ∧
    -Real.log (1216243 / 1228800) ≤ (2054297 / 200000000) := by
  have h := checkLog_sound (w := (12557 / 2445043)) (n := 12)
    (lo := (2567871 / 250000000)) (hi := (2054297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1216243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1216243) = 1/(1216243 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_4 : (914648719 / 400000000) ≤ xi (12557 / 1228800) ∧ xi (12557 / 1228800) ≤ (4573243603 / 2000000000) ∧
    (1148446641 / 500000000) ≤ kap (12557 / 1228800) ∧ kap (12557 / 1228800) ≤ (1148446643 / 500000000) := by
  have h := endpoint_bounds (v := ((12557 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_4.1 (by convert! log_c_4.1 using 1; norm_num)
    log_v_4.2 (by convert! log_c_4.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_5 : (4578173791 / 1000000000) ≤ -Real.log (50497 / 4915200) ∧
    -Real.log (50497 / 4915200) ≤ (2289086899 / 500000000) := by
  have h := checkLog_sound (w := (26303 / 127297)) (n := 12)
    (lo := (419290711 / 1000000000)) (hi := (52411339 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 50497) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 50497) = 1/(50497 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_5 : (10326779 / 1000000000) ≤ -Real.log (4864703 / 4915200) ∧
    -Real.log (4864703 / 4915200) ≤ (516339 / 50000000) := by
  have h := checkLog_sound (w := (50497 / 9779903)) (n := 12)
    (lo := (10326779 / 1000000000)) (hi := (516339 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4864703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4864703) = 1/(4864703 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_5 : (4567847011 / 2000000000) ≤ xi (50497 / 4915200) ∧ xi (50497 / 4915200) ≤ (4567847019 / 2000000000) ∧
    (458850057 / 200000000) ≤ kap (50497 / 4915200) ∧ kap (50497 / 4915200) ≤ (2294250289 / 1000000000) := by
  have h := endpoint_bounds (v := ((50497 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_5.1 (by convert! log_c_5.1 using 1; norm_num)
    log_v_5.2 (by convert! log_c_5.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_6 : (57160761 / 12500000) ≤ -Real.log (8461 / 819200) ∧
    -Real.log (8461 / 819200) ≤ (4572860887 / 1000000000) := by
  have h := checkLog_sound (w := (4339 / 21261)) (n := 12)
    (lo := (2069889 / 5000000)) (hi := (413977801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 8461) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12800 / 8461) = 1/(8461 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_6 : (2595519 / 250000000) ≤ -Real.log (810739 / 819200) ∧
    -Real.log (810739 / 819200) ≤ (10382077 / 1000000000) := by
  have h := checkLog_sound (w := (8461 / 1629939)) (n := 12)
    (lo := (2595519 / 250000000)) (hi := (10382077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 810739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 810739) = 1/(810739 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_6 : (4562478803 / 2000000000) ≤ xi (8461 / 819200) ∧ xi (8461 / 819200) ≤ (4562478811 / 2000000000) ∧
    (1145810739 / 500000000) ≤ kap (8461 / 819200) ∧ kap (8461 / 819200) ≤ (1145810741 / 500000000) := by
  have h := endpoint_bounds (v := ((8461 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_6.1 (by convert! log_c_6.1 using 1; norm_num)
    log_v_6.2 (by convert! log_c_6.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_7 : (285473503 / 62500000) ≤ -Real.log (10207 / 983040) ∧
    -Real.log (10207 / 983040) ≤ (913515211 / 200000000) := by
  have h := checkLog_sound (w := (5153 / 25567)) (n := 12)
    (lo := (51086621 / 125000000)) (hi := (408692969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 10207) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(15360 / 10207) = 1/(10207 / 983040) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_7 : (10437377 / 1000000000) ≤ -Real.log (972833 / 983040) ∧
    -Real.log (972833 / 983040) ≤ (5218689 / 500000000) := by
  have h := checkLog_sound (w := (10207 / 1955873)) (n := 12)
    (lo := (10437377 / 1000000000)) (hi := (5218689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983040 / 972833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983040 / 972833) = 1/(972833 / 983040) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_7 : (455713867 / 200000000) ≤ xi (10207 / 983040) ∧ xi (10207 / 983040) ≤ (2278569339 / 1000000000) ∧
    (183120537 / 80000000) ≤ kap (10207 / 983040) ∧ kap (10207 / 983040) ≤ (4578013433 / 2000000000) := by
  have h := endpoint_bounds (v := ((10207 / 983040) : ℝ)) (by norm_num) (by norm_num)
    log_v_7.1 (by convert! log_c_7.1 using 1; norm_num)
    log_v_7.2 (by convert! log_c_7.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_8 : (2281159499 / 500000000) ≤ -Real.log (6413 / 614400) ∧
    -Real.log (6413 / 614400) ≤ (912463801 / 200000000) := by
  have h := checkLog_sound (w := (3187 / 16013)) (n := 12)
    (lo := (201717959 / 500000000)) (hi := (403435919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6413) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9600 / 6413) = 1/(6413 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_8 : (10492681 / 1000000000) ≤ -Real.log (607987 / 614400) ∧
    -Real.log (607987 / 614400) ≤ (5246341 / 500000000) := by
  have h := checkLog_sound (w := (6413 / 1222387)) (n := 12)
    (lo := (10492681 / 1000000000)) (hi := (5246341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 607987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 607987) = 1/(607987 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_8 : (1137956579 / 500000000) ≤ xi (6413 / 614400) ∧ xi (6413 / 614400) ≤ (1137956581 / 500000000) ∧
    (4572811679 / 2000000000) ≤ kap (6413 / 614400) ∧ kap (6413 / 614400) ≤ (4572811687 / 2000000000) := by
  have h := endpoint_bounds (v := ((6413 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_8.1 (by convert! log_c_8.1 using 1; norm_num)
    log_v_8.2 (by convert! log_c_8.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_9 : (28481809 / 6250000) ≤ -Real.log (17191 / 1638400) ∧
    -Real.log (17191 / 1638400) ≤ (4557089447 / 1000000000) := by
  have h := checkLog_sound (w := (8409 / 42791)) (n := 12)
    (lo := (9955159 / 25000000)) (hi := (398206361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 17191) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25600 / 17191) = 1/(17191 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_9 : (2636997 / 250000000) ≤ -Real.log (1621209 / 1638400) ∧
    -Real.log (1621209 / 1638400) ≤ (10547989 / 1000000000) := by
  have h := checkLog_sound (w := (17191 / 3259609)) (n := 12)
    (lo := (2636997 / 250000000)) (hi := (10547989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638400 / 1621209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638400 / 1621209) = 1/(1621209 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_9 : (4546541451 / 2000000000) ≤ xi (17191 / 1638400) ∧ xi (17191 / 1638400) ≤ (4546541459 / 2000000000) ∧
    (1141909357 / 500000000) ≤ kap (17191 / 1638400) ∧ kap (17191 / 1638400) ≤ (1141909359 / 500000000) := by
  have h := endpoint_bounds (v := ((17191 / 1638400) : ℝ)) (by norm_num) (by norm_num)
    log_v_9.1 (by convert! log_c_9.1 using 1; norm_num)
    log_v_9.2 (by convert! log_c_9.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_10 : (284492943 / 62500000) ≤ -Real.log (25921 / 2457600) ∧
    -Real.log (25921 / 2457600) ≤ (910377419 / 200000000) := by
  have h := checkLog_sound (w := (12479 / 64321)) (n := 12)
    (lo := (49125501 / 125000000)) (hi := (393004009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 25921) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 25921) = 1/(25921 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_10 : (5301649 / 500000000) ≤ -Real.log (2431679 / 2457600) ∧
    -Real.log (2431679 / 2457600) ≤ (10603299 / 1000000000) := by
  have h := checkLog_sound (w := (25921 / 4889279)) (n := 12)
    (lo := (5301649 / 500000000)) (hi := (10603299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2431679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2431679) = 1/(2431679 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_10 : (4541283789 / 2000000000) ≤ xi (25921 / 2457600) ∧ xi (25921 / 2457600) ≤ (4541283797 / 2000000000) ∧
    (2281245193 / 1000000000) ≤ kap (25921 / 2457600) ∧ kap (25921 / 2457600) ≤ (2281245197 / 1000000000) := by
  have h := endpoint_bounds (v := ((25921 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_10.1 (by convert! log_c_10.1 using 1; norm_num)
    log_v_10.2 (by convert! log_c_10.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_11 : (4546711661 / 1000000000) ≤ -Real.log (52111 / 4915200) ∧
    -Real.log (52111 / 4915200) ≤ (1136677917 / 250000000) := by
  have h := checkLog_sound (w := (24689 / 128911)) (n := 12)
    (lo := (387828581 / 1000000000)) (hi := (193914291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 52111) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 52111) = 1/(52111 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_11 : (10658611 / 1000000000) ≤ -Real.log (4863089 / 4915200) ∧
    -Real.log (4863089 / 4915200) ≤ (2664653 / 250000000) := by
  have h := checkLog_sound (w := (52111 / 9778289)) (n := 12)
    (lo := (10658611 / 1000000000)) (hi := (2664653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4863089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4863089) = 1/(4863089 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_11 : (4536053049 / 2000000000) ≤ xi (52111 / 4915200) ∧ xi (52111 / 4915200) ≤ (4536053057 / 2000000000) ∧
    (142417821 / 62500000) ≤ kap (52111 / 4915200) ∧ kap (52111 / 4915200) ≤ (113934257 / 50000000) := by
  have h := endpoint_bounds (v := ((52111 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_11.1 (by convert! log_c_11.1 using 1; norm_num)
    log_v_11.2 (by convert! log_c_11.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_12 : (4541562881 / 1000000000) ≤ -Real.log (873 / 81920) ∧
    -Real.log (873 / 81920) ≤ (567695361 / 125000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1280 / 873) = 1/(873 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_12 : (10713927 / 1000000000) ≤ -Real.log (81047 / 81920) ∧
    -Real.log (81047 / 81920) ≤ (1339241 / 125000000) := by
  have h := checkLog_sound (w := (873 / 162967)) (n := 12)
    (lo := (10713927 / 1000000000)) (hi := (1339241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81920 / 81047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81920 / 81047) = 1/(81047 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_12 : (4530848953 / 2000000000) ≤ xi (873 / 81920) ∧ xi (873 / 81920) ≤ (4530848961 / 2000000000) ∧
    (569034601 / 250000000) ≤ kap (873 / 81920) ∧ kap (873 / 81920) ≤ (284517301 / 125000000) := by
  have h := endpoint_bounds (v := ((873 / 81920) : ℝ)) (by norm_num) (by norm_num)
    log_v_12.1 (by convert! log_c_12.1 using 1; norm_num)
    log_v_12.2 (by convert! log_c_12.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_13 : (181457619 / 40000000) ≤ -Real.log (52649 / 4915200) ∧
    -Real.log (52649 / 4915200) ≤ (2268220241 / 500000000) := by
  have h := checkLog_sound (w := (24151 / 129449)) (n := 12)
    (lo := (75511479 / 200000000)) (hi := (94389349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 52649) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 52649) = 1/(52649 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_13 : (10769247 / 1000000000) ≤ -Real.log (4862551 / 4915200) ∧
    -Real.log (4862551 / 4915200) ≤ (336539 / 31250000) := by
  have h := checkLog_sound (w := (52649 / 9777751)) (n := 12)
    (lo := (10769247 / 1000000000)) (hi := (336539 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4862551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4862551) = 1/(4862551 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_13 : (4525671227 / 2000000000) ≤ xi (52649 / 4915200) ∧ xi (52649 / 4915200) ≤ (905134247 / 400000000) ∧
    (2273604861 / 1000000000) ≤ kap (52649 / 4915200) ∧ kap (52649 / 4915200) ≤ (454720973 / 200000000) := by
  have h := endpoint_bounds (v := ((52649 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_13.1 (by convert! log_c_13.1 using 1; norm_num)
    log_v_13.2 (by convert! log_c_13.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_14 : (2265672087 / 500000000) ≤ -Real.log (26459 / 2457600) ∧
    -Real.log (26459 / 2457600) ≤ (4531344181 / 1000000000) := by
  have h := checkLog_sound (w := (11941 / 64859)) (n := 12)
    (lo := (186230547 / 500000000)) (hi := (74492219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 26459) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 26459) = 1/(26459 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_14 : (10824569 / 1000000000) ≤ -Real.log (2431141 / 2457600) ∧
    -Real.log (2431141 / 2457600) ≤ (1082457 / 100000000) := by
  have h := checkLog_sound (w := (26459 / 4888741)) (n := 12)
    (lo := (10824569 / 1000000000)) (hi := (1082457 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2431141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2431141) = 1/(2431141 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_14 : (1130129901 / 500000000) ≤ xi (26459 / 2457600) ∧ xi (26459 / 2457600) ≤ (1130129903 / 500000000) ∧
    (4542168743 / 2000000000) ≤ kap (26459 / 2457600) ∧ kap (26459 / 2457600) ≤ (4542168751 / 2000000000) := by
  have h := endpoint_bounds (v := ((26459 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_14.1 (by convert! log_c_14.1 using 1; norm_num)
    log_v_14.2 (by convert! log_c_14.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_15 : (2263136857 / 500000000) ≤ -Real.log (17729 / 1638400) ∧
    -Real.log (17729 / 1638400) ≤ (4526273721 / 1000000000) := by
  have h := checkLog_sound (w := (7871 / 43329)) (n := 12)
    (lo := (183695317 / 500000000)) (hi := (73478127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 17729) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25600 / 17729) = 1/(17729 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_15 : (5439947 / 500000000) ≤ -Real.log (1620671 / 1638400) ∧
    -Real.log (1620671 / 1638400) ≤ (2175979 / 200000000) := by
  have h := checkLog_sound (w := (17729 / 3259071)) (n := 12)
    (lo := (5439947 / 500000000)) (hi := (2175979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638400 / 1620671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638400 / 1620671) = 1/(1620671 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_15 : (4515393819 / 2000000000) ≤ xi (17729 / 1638400) ∧ xi (17729 / 1638400) ≤ (4515393827 / 2000000000) ∧
    (567144201 / 250000000) ≤ kap (17729 / 1638400) ∧ kap (17729 / 1638400) ≤ (283572101 / 125000000) := by
  have h := endpoint_bounds (v := ((17729 / 1638400) : ℝ)) (by norm_num) (by norm_num)
    log_v_15.1 (by convert! log_c_15.1 using 1; norm_num)
    log_v_15.2 (by convert! log_c_15.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


