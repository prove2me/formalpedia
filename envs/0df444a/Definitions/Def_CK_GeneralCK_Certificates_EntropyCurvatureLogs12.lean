-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs12
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:41:50.861988+00:00
-- url     : https://prove2.me/theorems/6176318d-9469-4727-a702-10f28237a96a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs12` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs12` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs12` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs12 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs12.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_192 : (2758059367 / 1000000000) ≤ -Real.log (19481 / 307200) ∧
    -Real.log (19481 / 307200) ≤ (2758059371 / 1000000000) := by
  have h := checkLog_sound (w := (18919 / 57881)) (n := 12)
    (lo := (678617827 / 1000000000)) (hi := (169654457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 19481) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(38400 / 19481) = 1/(19481 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_192 : (65514691 / 1000000000) ≤ -Real.log (287719 / 307200) ∧
    -Real.log (287719 / 307200) ≤ (16378673 / 250000000) := by
  have h := checkLog_sound (w := (19481 / 594919)) (n := 12)
    (lo := (65514691 / 1000000000)) (hi := (16378673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 287719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 287719) = 1/(287719 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_192 : (107701787 / 80000000) ≤ xi (19481 / 307200) ∧ xi (19481 / 307200) ≤ (67313617 / 50000000) ∧
    (1411787029 / 1000000000) ≤ kap (19481 / 307200) ∧ kap (19481 / 307200) ≤ (2823574063 / 2000000000) := by
  have h := endpoint_bounds (v := ((19481 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_192.1 (by convert! log_c_192.1 using 1; norm_num)
    log_v_192.2 (by convert! log_c_192.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_193 : (686086377 / 250000000) ≤ -Real.log (395 / 6144) ∧
    -Real.log (395 / 6144) ≤ (343043189 / 125000000) := by
  have h := checkLog_sound (w := (373 / 1163)) (n := 12)
    (lo := (20778249 / 31250000)) (hi := (664903969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 395) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(768 / 395) = 1/(395 / 6144) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_193 : (66450069 / 1000000000) ≤ -Real.log (5749 / 6144) ∧
    -Real.log (5749 / 6144) ≤ (6645007 / 100000000) := by
  have h := checkLog_sound (w := (395 / 11893)) (n := 12)
    (lo := (66450069 / 1000000000)) (hi := (6645007 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6144 / 5749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6144 / 5749) = 1/(5749 / 6144) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_193 : (1338947719 / 1000000000) ≤ xi (395 / 6144) ∧ xi (395 / 6144) ≤ (2677895443 / 2000000000) ∧
    (2810795577 / 2000000000) ≤ kap (395 / 6144) ∧ kap (395 / 6144) ≤ (1405397791 / 1000000000) := by
  have h := endpoint_bounds (v := ((395 / 6144) : ℝ)) (by norm_num) (by norm_num)
    log_v_193.1 (by convert! log_c_193.1 using 1; norm_num)
    log_v_193.2 (by convert! log_c_193.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_194 : (2730817177 / 1000000000) ≤ -Real.log (6673 / 102400) ∧
    -Real.log (6673 / 102400) ≤ (2730817181 / 1000000000) := by
  have h := checkLog_sound (w := (6127 / 19473)) (n := 12)
    (lo := (651375637 / 1000000000)) (hi := (325687819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 6673) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12800 / 6673) = 1/(6673 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_194 : (33693161 / 500000000) ≤ -Real.log (95727 / 102400) ∧
    -Real.log (95727 / 102400) ≤ (67386323 / 1000000000) := by
  have h := checkLog_sound (w := (6673 / 198127)) (n := 12)
    (lo := (33693161 / 500000000)) (hi := (67386323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 95727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 95727) = 1/(95727 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_194 : (1331715427 / 1000000000) ≤ xi (6673 / 102400) ∧ xi (6673 / 102400) ≤ (2663430859 / 2000000000) ∧
    (2798203499 / 2000000000) ≤ kap (6673 / 102400) ∧ kap (6673 / 102400) ≤ (174887719 / 125000000) := by
  have h := endpoint_bounds (v := ((6673 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_194.1 (by convert! log_c_194.1 using 1; norm_num)
    log_v_194.2 (by convert! log_c_194.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_195 : (2717469421 / 1000000000) ≤ -Real.log (317 / 4800) ∧
    -Real.log (317 / 4800) ≤ (108698777 / 40000000) := by
  have h := checkLog_sound (w := (283 / 917)) (n := 12)
    (lo := (638027881 / 1000000000)) (hi := (319013941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600 / 317) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(600 / 317) = 1/(317 / 4800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_195 : (17080863 / 250000000) ≤ -Real.log (4483 / 4800) ∧
    -Real.log (4483 / 4800) ≤ (68323453 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 9283)) (n := 12)
    (lo := (17080863 / 250000000)) (hi := (68323453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 4483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4800 / 4483) = 1/(4483 / 4800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_195 : (165571623 / 125000000) ≤ xi (317 / 4800) ∧ xi (317 / 4800) ≤ (2649145973 / 2000000000) ∧
    (2785792873 / 2000000000) ≤ kap (317 / 4800) ∧ kap (317 / 4800) ≤ (1392896439 / 1000000000) := by
  have h := endpoint_bounds (v := ((317 / 4800) : ℝ)) (by norm_num) (by norm_num)
    log_v_195.1 (by convert! log_c_195.1 using 1; norm_num)
    log_v_195.2 (by convert! log_c_195.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_196 : (676074371 / 250000000) ≤ -Real.log (20557 / 307200) ∧
    -Real.log (20557 / 307200) ≤ (169018593 / 62500000) := by
  have h := checkLog_sound (w := (17843 / 58957)) (n := 12)
    (lo := (78106993 / 125000000)) (hi := (124971189 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 20557) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(38400 / 20557) = 1/(20557 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_196 : (34630731 / 500000000) ≤ -Real.log (286643 / 307200) ∧
    -Real.log (286643 / 307200) ≤ (69261463 / 1000000000) := by
  have h := checkLog_sound (w := (20557 / 593843)) (n := 12)
    (lo := (34630731 / 500000000)) (hi := (69261463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 286643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 286643) = 1/(286643 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_196 : (2635036021 / 2000000000) ≤ xi (20557 / 307200) ∧ xi (20557 / 307200) ≤ (1317518013 / 1000000000) ∧
    (1386779473 / 1000000000) ≤ kap (20557 / 307200) ∧ kap (20557 / 307200) ≤ (2773558951 / 2000000000) := by
  have h := endpoint_bounds (v := ((20557 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_196.1 (by convert! log_c_196.1 using 1; norm_num)
    log_v_196.2 (by convert! log_c_196.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_197 : (2691296793 / 1000000000) ≤ -Real.log (3471 / 51200) ∧
    -Real.log (3471 / 51200) ≤ (2691296797 / 1000000000) := by
  have h := checkLog_sound (w := (2929 / 9871)) (n := 12)
    (lo := (611855253 / 1000000000)) (hi := (305927627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3471) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6400 / 3471) = 1/(3471 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_197 : (2193761 / 31250000) ≤ -Real.log (47729 / 51200) ∧
    -Real.log (47729 / 51200) ≤ (70200353 / 1000000000) := by
  have h := checkLog_sound (w := (3471 / 98929)) (n := 12)
    (lo := (2193761 / 31250000)) (hi := (70200353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 47729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 47729) = 1/(47729 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_197 : (65527411 / 50000000) ≤ xi (3471 / 51200) ∧ xi (3471 / 51200) ≤ (524219289 / 400000000) ∧
    (552299429 / 400000000) ≤ kap (3471 / 51200) ∧ kap (3471 / 51200) ≤ (55229943 / 40000000) := by
  have h := endpoint_bounds (v := ((3471 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_197.1 (by convert! log_c_197.1 using 1; norm_num)
    log_v_197.2 (by convert! log_c_197.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_198 : (1339231477 / 500000000) ≤ -Real.log (4219 / 61440) ∧
    -Real.log (4219 / 61440) ≤ (1339231479 / 500000000) := by
  have h := checkLog_sound (w := (3461 / 11899)) (n := 12)
    (lo := (299510707 / 500000000)) (hi := (119804283 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 4219) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7680 / 4219) = 1/(4219 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_198 : (17785031 / 250000000) ≤ -Real.log (57221 / 61440) ∧
    -Real.log (57221 / 61440) ≤ (569121 / 8000000) := by
  have h := checkLog_sound (w := (4219 / 118661)) (n := 12)
    (lo := (17785031 / 250000000)) (hi := (569121 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61440 / 57221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61440 / 57221) = 1/(57221 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_198 : (2607322829 / 2000000000) ≤ xi (4219 / 61440) ∧ xi (4219 / 61440) ≤ (1303661417 / 1000000000) ∧
    (1374801539 / 1000000000) ≤ kap (4219 / 61440) ∧ kap (4219 / 61440) ≤ (2749603083 / 2000000000) := by
  have h := endpoint_bounds (v := ((4219 / 61440) : ℝ)) (by norm_num) (by norm_num)
    log_v_198.1 (by convert! log_c_198.1 using 1; norm_num)
    log_v_198.2 (by convert! log_c_198.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_199 : (2665791737 / 1000000000) ≤ -Real.log (5341 / 76800) ∧
    -Real.log (5341 / 76800) ≤ (2665791741 / 1000000000) := by
  have h := checkLog_sound (w := (4259 / 14941)) (n := 12)
    (lo := (586350197 / 1000000000)) (hi := (293175099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 5341) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(9600 / 5341) = 1/(5341 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_199 : (72080781 / 1000000000) ≤ -Real.log (71459 / 76800) ∧
    -Real.log (71459 / 76800) ≤ (36040391 / 500000000) := by
  have h := checkLog_sound (w := (5341 / 148259)) (n := 12)
    (lo := (72080781 / 1000000000)) (hi := (36040391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 71459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 71459) = 1/(71459 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_199 : (518742191 / 400000000) ≤ xi (5341 / 76800) ∧ xi (5341 / 76800) ≤ (32421387 / 25000000) ∧
    (1368936259 / 1000000000) ≤ kap (5341 / 76800) ∧ kap (5341 / 76800) ≤ (2737872523 / 2000000000) := by
  have h := endpoint_bounds (v := ((5341 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_199.1 (by convert! log_c_199.1 using 1; norm_num)
    log_v_199.2 (by convert! log_c_199.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_200 : (82914971 / 31250000) ≤ -Real.log (7211 / 102400) ∧
    -Real.log (7211 / 102400) ≤ (663319769 / 250000000) := by
  have h := checkLog_sound (w := (5589 / 20011)) (n := 12)
    (lo := (143459383 / 250000000)) (hi := (573837533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 7211) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12800 / 7211) = 1/(7211 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_200 : (73022323 / 1000000000) ≤ -Real.log (95189 / 102400) ∧
    -Real.log (95189 / 102400) ≤ (18255581 / 250000000) := by
  have h := checkLog_sound (w := (7211 / 197589)) (n := 12)
    (lo := (73022323 / 1000000000)) (hi := (18255581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 95189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 95189) = 1/(95189 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_200 : (645064187 / 500000000) ≤ xi (7211 / 102400) ∧ xi (7211 / 102400) ≤ (2580256753 / 2000000000) ∧
    (545260279 / 400000000) ≤ kap (7211 / 102400) ∧ kap (7211 / 102400) ≤ (13631507 / 10000000) := by
  have h := endpoint_bounds (v := ((7211 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_200.1 (by convert! log_c_200.1 using 1; norm_num)
    log_v_200.2 (by convert! log_c_200.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_201 : (1320460521 / 500000000) ≤ -Real.log (10951 / 153600) ∧
    -Real.log (10951 / 153600) ≤ (1320460523 / 500000000) := by
  have h := checkLog_sound (w := (8249 / 30151)) (n := 12)
    (lo := (280739751 / 500000000)) (hi := (561479503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 10951) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(19200 / 10951) = 1/(10951 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_201 : (73964753 / 1000000000) ≤ -Real.log (142649 / 153600) ∧
    -Real.log (142649 / 153600) ≤ (36982377 / 500000000) := by
  have h := checkLog_sound (w := (10951 / 296249)) (n := 12)
    (lo := (73964753 / 1000000000)) (hi := (36982377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 142649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 142649) = 1/(142649 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_201 : (10027173 / 7812500) ≤ xi (10951 / 153600) ∧ xi (10951 / 153600) ≤ (2566956293 / 2000000000) ∧
    (542977159 / 400000000) ≤ kap (10951 / 153600) ∧ kap (10951 / 153600) ≤ (13574429 / 10000000) := by
  have h := endpoint_bounds (v := ((10951 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_201.1 (by convert! log_c_201.1 using 1; norm_num)
    log_v_201.2 (by convert! log_c_201.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_202 : (1308326959 / 500000000) ≤ -Real.log (187 / 2560) ∧
    -Real.log (187 / 2560) ≤ (1308326961 / 500000000) := by
  have h := checkLog_sound (w := (133 / 507)) (n := 12)
    (lo := (268606189 / 500000000)) (hi := (537212379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 187) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 187) = 1/(187 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_202 : (75852281 / 1000000000) ≤ -Real.log (2373 / 2560) ∧
    -Real.log (2373 / 2560) ≤ (37926141 / 500000000) := by
  have h := checkLog_sound (w := (187 / 4933)) (n := 12)
    (lo := (75852281 / 1000000000)) (hi := (37926141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2373) = 1/(2373 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_202 : (635200409 / 500000000) ≤ xi (187 / 2560) ∧ xi (187 / 2560) ≤ (2540801641 / 2000000000) ∧
    (2692506199 / 2000000000) ≤ kap (187 / 2560) ∧ kap (187 / 2560) ≤ (673126551 / 500000000) := by
  have h := endpoint_bounds (v := ((187 / 2560) : ℝ)) (by norm_num) (by norm_num)
    log_v_202.1 (by convert! log_c_202.1 using 1; norm_num)
    log_v_202.2 (by convert! log_c_202.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_203 : (2592961763 / 1000000000) ≤ -Real.log (11489 / 153600) ∧
    -Real.log (11489 / 153600) ≤ (2592961767 / 1000000000) := by
  have h := checkLog_sound (w := (7711 / 30689)) (n := 12)
    (lo := (513520223 / 1000000000)) (hi := (16047507 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 11489) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(19200 / 11489) = 1/(11489 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_203 : (38871689 / 500000000) ≤ -Real.log (142111 / 153600) ∧
    -Real.log (142111 / 153600) ≤ (77743379 / 1000000000) := by
  have h := checkLog_sound (w := (11489 / 295711)) (n := 12)
    (lo := (38871689 / 500000000)) (hi := (77743379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 142111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 142111) = 1/(142111 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_203 : (157201149 / 125000000) ≤ xi (11489 / 153600) ∧ xi (11489 / 153600) ≤ (2515218389 / 2000000000) ∧
    (2670705141 / 2000000000) ≤ kap (11489 / 153600) ∧ kap (11489 / 153600) ≤ (1335352573 / 1000000000) := by
  have h := endpoint_bounds (v := ((11489 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_203.1 (by convert! log_c_203.1 using 1; norm_num)
    log_v_203.2 (by convert! log_c_203.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_204 : (2569817959 / 1000000000) ≤ -Real.log (5879 / 76800) ∧
    -Real.log (5879 / 76800) ≤ (2569817963 / 1000000000) := by
  have h := checkLog_sound (w := (3721 / 15479)) (n := 12)
    (lo := (490376419 / 1000000000)) (hi := (24518821 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 5879) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(9600 / 5879) = 1/(5879 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_204 : (39819029 / 500000000) ≤ -Real.log (70921 / 76800) ∧
    -Real.log (70921 / 76800) ≤ (79638059 / 1000000000) := by
  have h := checkLog_sound (w := (5879 / 147721)) (n := 12)
    (lo := (39819029 / 500000000)) (hi := (79638059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 70921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 70921) = 1/(70921 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_204 : (24901799 / 20000000) ≤ xi (5879 / 76800) ∧ xi (5879 / 76800) ≤ (498035981 / 400000000) ∧
    (2649456017 / 2000000000) ≤ kap (5879 / 76800) ∧ kap (5879 / 76800) ≤ (1324728011 / 1000000000) := by
  have h := endpoint_bounds (v := ((5879 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_204.1 (by convert! log_c_204.1 using 1; norm_num)
    log_v_204.2 (by convert! log_c_204.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_205 : (9949991 / 3906250) ≤ -Real.log (4009 / 51200) ∧
    -Real.log (4009 / 51200) ≤ (25471977 / 10000000) := by
  have h := checkLog_sound (w := (2391 / 10409)) (n := 12)
    (lo := (116939039 / 250000000)) (hi := (467756157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4009) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6400 / 4009) = 1/(4009 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_205 : (16307267 / 200000000) ≤ -Real.log (47191 / 51200) ∧
    -Real.log (47191 / 51200) ≤ (5096021 / 62500000) := by
  have h := checkLog_sound (w := (4009 / 98391)) (n := 12)
    (lo := (16307267 / 200000000)) (hi := (5096021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 47191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 47191) = 1/(47191 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_205 : (30820767 / 25000000) ≤ xi (4009 / 51200) ∧ xi (4009 / 51200) ≤ (493132273 / 400000000) ∧
    (2628734031 / 2000000000) ≤ kap (4009 / 51200) ∧ kap (4009 / 51200) ≤ (657183509 / 500000000) := by
  have h := endpoint_bounds (v := ((4009 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_205.1 (by convert! log_c_205.1 using 1; norm_num)
    log_v_205.2 (by convert! log_c_205.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_206 : (631269453 / 250000000) ≤ -Real.log (1537 / 19200) ∧
    -Real.log (1537 / 19200) ≤ (315634727 / 125000000) := by
  have h := checkLog_sound (w := (863 / 3937)) (n := 12)
    (lo := (27852267 / 62500000)) (hi := (445636273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 1537) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2400 / 1537) = 1/(1537 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_206 : (41719111 / 500000000) ≤ -Real.log (17663 / 19200) ∧
    -Real.log (17663 / 19200) ≤ (83438223 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 36863)) (n := 12)
    (lo := (41719111 / 500000000)) (hi := (83438223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 17663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 17663) = 1/(17663 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_206 : (2441639589 / 2000000000) ≤ xi (1537 / 19200) ∧ xi (1537 / 19200) ≤ (1220819797 / 1000000000) ∧
    (1304258017 / 1000000000) ≤ kap (1537 / 19200) ∧ kap (1537 / 19200) ≤ (2608516039 / 2000000000) := by
  have h := endpoint_bounds (v := ((1537 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_206.1 (by convert! log_c_206.1 using 1; norm_num)
    log_v_206.2 (by convert! log_c_206.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_207 : (312929581 / 125000000) ≤ -Real.log (2513 / 30720) ∧
    -Real.log (2513 / 30720) ≤ (625859163 / 250000000) := by
  have h := checkLog_sound (w := (1327 / 6353)) (n := 12)
    (lo := (105998777 / 250000000)) (hi := (423995109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 2513) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3840 / 2513) = 1/(2513 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_207 : (42671867 / 500000000) ≤ -Real.log (28207 / 30720) ∧
    -Real.log (28207 / 30720) ≤ (17068747 / 200000000) := by
  have h := checkLog_sound (w := (2513 / 58927)) (n := 12)
    (lo := (42671867 / 500000000)) (hi := (17068747 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30720 / 28207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30720 / 28207) = 1/(28207 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_207 : (2418092913 / 2000000000) ≤ xi (2513 / 30720) ∧ xi (2513 / 30720) ≤ (1209046459 / 1000000000) ∧
    (1294390191 / 1000000000) ≤ kap (2513 / 30720) ∧ kap (2513 / 30720) ≤ (2588780387 / 2000000000) := by
  have h := endpoint_bounds (v := ((2513 / 30720) : ℝ)) (by norm_num) (by norm_num)
    log_v_207.1 (by convert! log_c_207.1 using 1; norm_num)
    log_v_207.2 (by convert! log_c_207.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


