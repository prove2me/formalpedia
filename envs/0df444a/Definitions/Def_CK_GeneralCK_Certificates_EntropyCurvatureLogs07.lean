-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs07
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:44:05.984344+00:00
-- url     : https://prove2.me/theorems/5e698fe3-c9c0-494f-b24b-c58a06559a66
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs07` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs07` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs07` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs07 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs07.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_112 : (3757000771 / 1000000000) ≤ -Real.log (28697 / 1228800) ∧
    -Real.log (28697 / 1228800) ≤ (3757000777 / 1000000000) := by
  have h := checkLog_sound (w := (9703 / 67097)) (n := 12)
    (lo := (291264871 / 1000000000)) (hi := (36408109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 28697) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 28697) = 1/(28697 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_112 : (2953837 / 125000000) ≤ -Real.log (1200103 / 1228800) ∧
    -Real.log (1200103 / 1228800) ≤ (23630697 / 1000000000) := by
  have h := checkLog_sound (w := (28697 / 2428903)) (n := 12)
    (lo := (2953837 / 125000000)) (hi := (23630697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1200103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1200103) = 1/(1200103 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_112 : (1866685037 / 1000000000) ≤ xi (28697 / 1228800) ∧ xi (28697 / 1228800) ≤ (3733370081 / 2000000000) ∧
    (3780631467 / 2000000000) ≤ kap (28697 / 1228800) ∧ kap (28697 / 1228800) ≤ (1890315737 / 1000000000) := by
  have h := endpoint_bounds (v := ((28697 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_112.1 (by convert! log_c_112.1 using 1; norm_num)
    log_v_112.2 (by convert! log_c_112.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_113 : (3747670631 / 1000000000) ≤ -Real.log (14483 / 614400) ∧
    -Real.log (14483 / 614400) ≤ (3747670637 / 1000000000) := by
  have h := checkLog_sound (w := (4717 / 33683)) (n := 12)
    (lo := (281934731 / 1000000000)) (hi := (70483683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 14483) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 14483) = 1/(14483 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_113 : (23854869 / 1000000000) ≤ -Real.log (599917 / 614400) ∧
    -Real.log (599917 / 614400) ≤ (2385487 / 100000000) := by
  have h := checkLog_sound (w := (14483 / 1214317)) (n := 12)
    (lo := (23854869 / 1000000000)) (hi := (2385487 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 599917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 599917) = 1/(599917 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_113 : (3723815761 / 2000000000) ≤ xi (14483 / 614400) ∧ xi (14483 / 614400) ≤ (465476971 / 250000000) ∧
    (7543051 / 4000000) ≤ kap (14483 / 614400) ∧ kap (14483 / 614400) ≤ (3771525507 / 2000000000) := by
  have h := endpoint_bounds (v := ((14483 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_113.1 (by convert! log_c_113.1 using 1; norm_num)
    log_v_113.2 (by convert! log_c_113.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_114 : (3738426737 / 1000000000) ≤ -Real.log (1949 / 81920) ∧
    -Real.log (1949 / 81920) ≤ (3738426743 / 1000000000) := by
  have h := checkLog_sound (w := (611 / 4509)) (n := 12)
    (lo := (272690837 / 1000000000)) (hi := (136345419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1949) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2560 / 1949) = 1/(1949 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_114 : (6019773 / 250000000) ≤ -Real.log (79971 / 81920) ∧
    -Real.log (79971 / 81920) ≤ (24079093 / 1000000000) := by
  have h := checkLog_sound (w := (1949 / 161891)) (n := 12)
    (lo := (6019773 / 250000000)) (hi := (24079093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81920 / 79971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81920 / 79971) = 1/(79971 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_114 : (928586911 / 500000000) ≤ xi (1949 / 81920) ∧ xi (1949 / 81920) ≤ (3714347651 / 2000000000) ∧
    (3762505829 / 2000000000) ≤ kap (1949 / 81920) ∧ kap (1949 / 81920) ≤ (940626459 / 500000000) := by
  have h := endpoint_bounds (v := ((1949 / 81920) : ℝ)) (by norm_num) (by norm_num)
    log_v_114.1 (by convert! log_c_114.1 using 1; norm_num)
    log_v_114.2 (by convert! log_c_114.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_115 : (466158439 / 125000000) ≤ -Real.log (461 / 19200) ∧
    -Real.log (461 / 19200) ≤ (1864633759 / 500000000) := by
  have h := checkLog_sound (w := (139 / 1061)) (n := 12)
    (lo := (65882903 / 250000000)) (hi := (263531613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600 / 461) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(600 / 461) = 1/(461 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_115 : (4860673 / 200000000) ≤ -Real.log (18739 / 19200) ∧
    -Real.log (18739 / 19200) ≤ (12151683 / 500000000) := by
  have h := checkLog_sound (w := (461 / 37939)) (n := 12)
    (lo := (4860673 / 200000000)) (hi := (12151683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 18739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 18739) = 1/(18739 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_115 : (1852482073 / 1000000000) ≤ xi (461 / 19200) ∧ xi (461 / 19200) ≤ (3704964153 / 2000000000) ∧
    (3753570877 / 2000000000) ≤ kap (461 / 19200) ∧ kap (461 / 19200) ≤ (938392721 / 500000000) := by
  have h := endpoint_bounds (v := ((461 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_115.1 (by convert! log_c_115.1 using 1; norm_num)
    log_v_115.2 (by convert! log_c_115.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_116 : (3720191417 / 1000000000) ≤ -Real.log (29773 / 1228800) ∧
    -Real.log (29773 / 1228800) ≤ (3720191423 / 1000000000) := by
  have h := checkLog_sound (w := (8627 / 68173)) (n := 12)
    (lo := (254455517 / 1000000000)) (hi := (127227759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 29773) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 29773) = 1/(29773 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_116 : (3065961 / 125000000) ≤ -Real.log (1199027 / 1228800) ∧
    -Real.log (1199027 / 1228800) ≤ (24527689 / 1000000000) := by
  have h := checkLog_sound (w := (29773 / 2427827)) (n := 12)
    (lo := (3065961 / 125000000)) (hi := (24527689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1199027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1199027) = 1/(1199027 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_116 : (230978983 / 125000000) ≤ xi (29773 / 1228800) ∧ xi (29773 / 1228800) ≤ (739132747 / 400000000) ∧
    (748943821 / 400000000) ≤ kap (29773 / 1228800) ∧ kap (29773 / 1228800) ≤ (468089889 / 250000000) := by
  have h := endpoint_bounds (v := ((29773 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_116.1 (by convert! log_c_116.1 using 1; norm_num)
    log_v_116.2 (by convert! log_c_116.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_117 : (3711196957 / 1000000000) ≤ -Real.log (5007 / 204800) ∧
    -Real.log (5007 / 204800) ≤ (3711196963 / 1000000000) := by
  have h := checkLog_sound (w := (1393 / 11407)) (n := 12)
    (lo := (245461057 / 1000000000)) (hi := (122730529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5007) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6400 / 5007) = 1/(5007 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_117 : (12376031 / 500000000) ≤ -Real.log (199793 / 204800) ∧
    -Real.log (199793 / 204800) ≤ (24752063 / 1000000000) := by
  have h := checkLog_sound (w := (5007 / 404593)) (n := 12)
    (lo := (12376031 / 500000000)) (hi := (24752063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 199793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 199793) = 1/(199793 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_117 : (1843222447 / 1000000000) ≤ xi (5007 / 204800) ∧ xi (5007 / 204800) ≤ (3686444901 / 2000000000) ∧
    (3735949019 / 2000000000) ≤ kap (5007 / 204800) ∧ kap (5007 / 204800) ≤ (1867974513 / 1000000000) := by
  have h := endpoint_bounds (v := ((5007 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_117.1 (by convert! log_c_117.1 using 1; norm_num)
    log_v_117.2 (by convert! log_c_117.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_118 : (925570669 / 250000000) ≤ -Real.log (30311 / 1228800) ∧
    -Real.log (30311 / 1228800) ≤ (1851141341 / 500000000) := by
  have h := checkLog_sound (w := (8089 / 68711)) (n := 12)
    (lo := (29568347 / 125000000)) (hi := (236546777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 30311) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 30311) = 1/(30311 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_118 : (12488243 / 500000000) ≤ -Real.log (1198489 / 1228800) ∧
    -Real.log (1198489 / 1228800) ≤ (24976487 / 1000000000) := by
  have h := checkLog_sound (w := (30311 / 2427289)) (n := 12)
    (lo := (12488243 / 500000000)) (hi := (24976487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1198489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1198489) = 1/(1198489 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_118 : (3677306189 / 2000000000) ≤ xi (30311 / 1228800) ∧ xi (30311 / 1228800) ≤ (919326549 / 500000000) ∧
    (1863629581 / 1000000000) ≤ kap (30311 / 1228800) ∧ kap (30311 / 1228800) ≤ (3727259169 / 2000000000) := by
  have h := endpoint_bounds (v := ((30311 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_118.1 (by convert! log_c_118.1 using 1; norm_num)
    log_v_118.2 (by convert! log_c_118.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_119 : (3693447159 / 1000000000) ≤ -Real.log (1529 / 61440) ∧
    -Real.log (1529 / 61440) ≤ (738689433 / 200000000) := by
  have h := checkLog_sound (w := (391 / 3449)) (n := 12)
    (lo := (227711259 / 1000000000)) (hi := (11385563 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920 / 1529) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1920 / 1529) = 1/(1529 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_119 : (25200961 / 1000000000) ≤ -Real.log (59911 / 61440) ∧
    -Real.log (59911 / 61440) ≤ (12600481 / 500000000) := by
  have h := checkLog_sound (w := (1529 / 121351)) (n := 12)
    (lo := (25200961 / 1000000000)) (hi := (12600481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61440 / 59911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61440 / 59911) = 1/(59911 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_119 : (3668246197 / 2000000000) ≤ xi (1529 / 61440) ∧ xi (1529 / 61440) ≤ (917061551 / 500000000) ∧
    (92966203 / 50000000) ≤ kap (1529 / 61440) ∧ kap (1529 / 61440) ≤ (3718648127 / 2000000000) := by
  have h := endpoint_bounds (v := ((1529 / 61440) : ℝ)) (by norm_num) (by norm_num)
    log_v_119.1 (by convert! log_c_119.1 using 1; norm_num)
    log_v_119.2 (by convert! log_c_119.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_120 : (28786633 / 7812500) ≤ -Real.log (10283 / 409600) ∧
    -Real.log (10283 / 409600) ≤ (368468903 / 100000000) := by
  have h := checkLog_sound (w := (2517 / 23083)) (n := 12)
    (lo := (54738281 / 250000000)) (hi := (14013 / 64000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 10283) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 10283) = 1/(10283 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_120 : (12712743 / 500000000) ≤ -Real.log (399317 / 409600) ∧
    -Real.log (399317 / 409600) ≤ (25425487 / 1000000000) := by
  have h := checkLog_sound (w := (10283 / 808917)) (n := 12)
    (lo := (12712743 / 500000000)) (hi := (25425487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 399317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 399317) = 1/(399317 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_120 : (3659263537 / 2000000000) ≤ xi (10283 / 409600) ∧ xi (10283 / 409600) ≤ (457407943 / 250000000) ∧
    (371011451 / 200000000) ≤ kap (10283 / 409600) ∧ kap (10283 / 409600) ≤ (3710114517 / 2000000000) := by
  have h := endpoint_bounds (v := ((10283 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_120.1 (by convert! log_c_120.1 using 1; norm_num)
    log_v_120.2 (by convert! log_c_120.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_121 : (3676006929 / 1000000000) ≤ -Real.log (15559 / 614400) ∧
    -Real.log (15559 / 614400) ≤ (735201387 / 200000000) := by
  have h := checkLog_sound (w := (3641 / 34759)) (n := 12)
    (lo := (210271029 / 1000000000)) (hi := (21027103 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 15559) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 15559) = 1/(15559 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_121 : (25650061 / 1000000000) ≤ -Real.log (598841 / 614400) ∧
    -Real.log (598841 / 614400) ≤ (12825031 / 500000000) := by
  have h := checkLog_sound (w := (15559 / 1213241)) (n := 12)
    (lo := (25650061 / 1000000000)) (hi := (12825031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 598841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 598841) = 1/(598841 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_121 : (3650356867 / 2000000000) ≤ xi (15559 / 614400) ∧ xi (15559 / 614400) ≤ (1825178437 / 1000000000) ∧
    (370165699 / 200000000) ≤ kap (15559 / 614400) ∧ kap (15559 / 614400) ≤ (3701656997 / 2000000000) := by
  have h := endpoint_bounds (v := ((15559 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_121.1 (by convert! log_c_121.1 using 1; norm_num)
    log_v_121.2 (by convert! log_c_121.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_122 : (733479913 / 200000000) ≤ -Real.log (31387 / 1228800) ∧
    -Real.log (31387 / 1228800) ≤ (3667399571 / 1000000000) := by
  have h := checkLog_sound (w := (7013 / 69787)) (n := 12)
    (lo := (40332733 / 200000000)) (hi := (100831833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 31387) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 31387) = 1/(31387 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_122 : (25874687 / 1000000000) ≤ -Real.log (1197413 / 1228800) ∧
    -Real.log (1197413 / 1228800) ≤ (101073 / 3906250) := by
  have h := checkLog_sound (w := (31387 / 2426213)) (n := 12)
    (lo := (25874687 / 1000000000)) (hi := (101073 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1197413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1197413) = 1/(1197413 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_122 : (3641524877 / 2000000000) ≤ xi (31387 / 1228800) ∧ xi (31387 / 1228800) ≤ (910381221 / 500000000) ∧
    (923318563 / 500000000) ≤ kap (31387 / 1228800) ∧ kap (31387 / 1228800) ≤ (3693274259 / 2000000000) := by
  have h := endpoint_bounds (v := ((31387 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_122.1 (by convert! log_c_122.1 using 1; norm_num)
    log_v_122.2 (by convert! log_c_122.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_123 : (731773131 / 200000000) ≤ -Real.log (1319 / 51200) ∧
    -Real.log (1319 / 51200) ≤ (3658865661 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 2919)) (n := 12)
    (lo := (38625951 / 200000000)) (hi := (48282439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1319) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1319) = 1/(1319 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_123 : (26099363 / 1000000000) ≤ -Real.log (49881 / 51200) ∧
    -Real.log (49881 / 51200) ≤ (6524841 / 250000000) := by
  have h := checkLog_sound (w := (1319 / 101081)) (n := 12)
    (lo := (26099363 / 1000000000)) (hi := (6524841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 49881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 49881) = 1/(49881 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_123 : (3632766291 / 2000000000) ≤ xi (1319 / 51200) ∧ xi (1319 / 51200) ≤ (1816383149 / 1000000000) ∧
    (1842482509 / 1000000000) ≤ kap (1319 / 51200) ∧ kap (1319 / 51200) ≤ (147398601 / 80000000) := by
  have h := endpoint_bounds (v := ((1319 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_123.1 (by convert! log_c_123.1 using 1; norm_num)
    log_v_123.2 (by convert! log_c_123.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_124 : (3650403957 / 1000000000) ≤ -Real.log (1277 / 49152) ∧
    -Real.log (1277 / 49152) ≤ (3650403963 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2813)) (n := 12)
    (lo := (184668057 / 1000000000)) (hi := (92334029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1536 / 1277) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1536 / 1277) = 1/(1277 / 49152) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_124 : (2632409 / 100000000) ≤ -Real.log (47875 / 49152) ∧
    -Real.log (47875 / 49152) ≤ (26324091 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 97027)) (n := 12)
    (lo := (2632409 / 100000000)) (hi := (26324091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49152 / 47875) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49152 / 47875) = 1/(47875 / 49152) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_124 : (1812039933 / 1000000000) ≤ xi (1277 / 49152) ∧ xi (1277 / 49152) ≤ (3624079873 / 2000000000) ∧
    (3676728047 / 2000000000) ≤ kap (1277 / 49152) ∧ kap (1277 / 49152) ≤ (1838364027 / 1000000000) := by
  have h := endpoint_bounds (v := ((1277 / 49152) : ℝ)) (by norm_num) (by norm_num)
    log_v_124.1 (by convert! log_c_124.1 using 1; norm_num)
    log_v_124.2 (by convert! log_c_124.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_125 : (3642013259 / 1000000000) ≤ -Real.log (16097 / 614400) ∧
    -Real.log (16097 / 614400) ≤ (728402653 / 200000000) := by
  have h := checkLog_sound (w := (3103 / 35297)) (n := 12)
    (lo := (176277359 / 1000000000)) (hi := (2203467 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 16097) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 16097) = 1/(16097 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_125 : (26548867 / 1000000000) ≤ -Real.log (598303 / 614400) ∧
    -Real.log (598303 / 614400) ≤ (6637217 / 250000000) := by
  have h := checkLog_sound (w := (16097 / 1212703)) (n := 12)
    (lo := (26548867 / 1000000000)) (hi := (6637217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 598303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 598303) = 1/(598303 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_125 : (3615464391 / 2000000000) ≤ xi (16097 / 614400) ∧ xi (16097 / 614400) ≤ (1807732199 / 1000000000) ∧
    (1834281063 / 1000000000) ≤ kap (16097 / 614400) ∧ kap (16097 / 614400) ≤ (3668562133 / 2000000000) := by
  have h := endpoint_bounds (v := ((16097 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_125.1 (by convert! log_c_125.1 using 1; norm_num)
    log_v_125.2 (by convert! log_c_125.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_126 : (181684619 / 50000000) ≤ -Real.log (10821 / 409600) ∧
    -Real.log (10821 / 409600) ≤ (1816846193 / 500000000) := by
  have h := checkLog_sound (w := (1979 / 23621)) (n := 12)
    (lo := (65608 / 390625)) (hi := (167956481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 10821) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 10821) = 1/(10821 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_126 : (13386847 / 500000000) ≤ -Real.log (398779 / 409600) ∧
    -Real.log (398779 / 409600) ≤ (5354739 / 200000000) := by
  have h := checkLog_sound (w := (10821 / 808379)) (n := 12)
    (lo := (13386847 / 500000000)) (hi := (5354739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 398779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 398779) = 1/(398779 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_126 : (721383737 / 400000000) ≤ xi (10821 / 409600) ∧ xi (10821 / 409600) ≤ (901729673 / 500000000) ∧
    (1830233037 / 1000000000) ≤ kap (10821 / 409600) ∧ kap (10821 / 409600) ≤ (3660466081 / 2000000000) := by
  have h := endpoint_bounds (v := ((10821 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_126.1 (by convert! log_c_126.1 using 1; norm_num)
    log_v_126.2 (by convert! log_c_126.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_127 : (1812720083 / 500000000) ≤ -Real.log (8183 / 307200) ∧
    -Real.log (8183 / 307200) ≤ (906360043 / 250000000) := by
  have h := checkLog_sound (w := (1417 / 17783)) (n := 12)
    (lo := (79852133 / 500000000)) (hi := (159704267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 8183) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9600 / 8183) = 1/(8183 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_127 : (26998573 / 1000000000) ≤ -Real.log (299017 / 307200) ∧
    -Real.log (299017 / 307200) ≤ (13499287 / 500000000) := by
  have h := checkLog_sound (w := (8183 / 606217)) (n := 12)
    (lo := (26998573 / 1000000000)) (hi := (13499287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 299017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 299017) = 1/(299017 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_127 : (449805199 / 250000000) ≤ xi (8183 / 307200) ∧ xi (8183 / 307200) ≤ (3598441599 / 2000000000) ∧
    (3652438739 / 2000000000) ≤ kap (8183 / 307200) ∧ kap (8183 / 307200) ≤ (1826219373 / 1000000000) := by
  have h := endpoint_bounds (v := ((8183 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_127.1 (by convert! log_c_127.1 using 1; norm_num)
    log_v_127.2 (by convert! log_c_127.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


