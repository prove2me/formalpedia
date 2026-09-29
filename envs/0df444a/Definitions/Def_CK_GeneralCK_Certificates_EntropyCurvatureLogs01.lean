-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs01
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:41:25.549593+00:00
-- url     : https://prove2.me/theorems/677ceab7-b6f0-45c8-b8cc-d4a71ea0a4b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs01` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs01` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs01` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs01 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs01.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_16 : (2260614417 / 500000000) ≤ -Real.log (3341 / 307200) ∧
    -Real.log (3341 / 307200) ≤ (4521228841 / 1000000000) := by
  have h := checkLog_sound (w := (1459 / 8141)) (n := 12)
    (lo := (181172877 / 500000000)) (hi := (72469151 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3341) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4800 / 3341) = 1/(3341 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_16 : (10935223 / 1000000000) ≤ -Real.log (303859 / 307200) ∧
    -Real.log (303859 / 307200) ≤ (1366903 / 125000000) := by
  have h := checkLog_sound (w := (3341 / 611059)) (n := 12)
    (lo := (10935223 / 1000000000)) (hi := (1366903 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 303859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 303859) = 1/(303859 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_16 : (451029361 / 200000000) ≤ xi (3341 / 307200) ∧ xi (3341 / 307200) ≤ (2255146809 / 1000000000) ∧
    (4532164057 / 2000000000) ≤ kap (3341 / 307200) ∧ kap (3341 / 307200) ≤ (906432813 / 400000000) := by
  have h := endpoint_bounds (v := ((3341 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_16.1 (by convert! log_c_16.1 using 1; norm_num)
    log_v_16.2 (by convert! log_c_16.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_17 : (4516209277 / 1000000000) ≤ -Real.log (2149 / 196608) ∧
    -Real.log (2149 / 196608) ≤ (1129052321 / 250000000) := by
  have h := checkLog_sound (w := (923 / 5221)) (n := 12)
    (lo := (357326197 / 1000000000)) (hi := (178663099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3072 / 2149) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3072 / 2149) = 1/(2149 / 196608) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_17 : (5495277 / 500000000) ≤ -Real.log (194459 / 196608) ∧
    -Real.log (194459 / 196608) ≤ (2198111 / 200000000) := by
  have h := checkLog_sound (w := (2149 / 391067)) (n := 12)
    (lo := (5495277 / 500000000)) (hi := (2198111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196608 / 194459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196608 / 194459) = 1/(194459 / 196608) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_17 : (2252609361 / 1000000000) ≤ xi (2149 / 196608) ∧ xi (2149 / 196608) ≤ (450521873 / 200000000) ∧
    (4527199831 / 2000000000) ≤ kap (2149 / 196608) ∧ kap (2149 / 196608) ≤ (4527199839 / 2000000000) := by
  have h := endpoint_bounds (v := ((2149 / 196608) : ℝ)) (by norm_num) (by norm_num)
    log_v_17.1 (by convert! log_c_17.1 using 1; norm_num)
    log_v_17.2 (by convert! log_c_17.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_18 : (451121479 / 100000000) ≤ -Real.log (8999 / 819200) ∧
    -Real.log (8999 / 819200) ≤ (4511214797 / 1000000000) := by
  have h := checkLog_sound (w := (3801 / 21799)) (n := 12)
    (lo := (35233171 / 100000000)) (hi := (352331711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 8999) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12800 / 8999) = 1/(8999 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_18 : (11045889 / 1000000000) ≤ -Real.log (810201 / 819200) ∧
    -Real.log (810201 / 819200) ≤ (1104589 / 100000000) := by
  have h := checkLog_sound (w := (8999 / 1629401)) (n := 12)
    (lo := (11045889 / 1000000000)) (hi := (1104589 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 810201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 810201) = 1/(810201 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_18 : (45001689 / 20000000) ≤ xi (8999 / 819200) ∧ xi (8999 / 819200) ≤ (1125042227 / 500000000) ∧
    (4522260679 / 2000000000) ≤ kap (8999 / 819200) ∧ kap (8999 / 819200) ≤ (4522260687 / 2000000000) := by
  have h := endpoint_bounds (v := ((8999 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_18.1 (by convert! log_c_18.1 using 1; norm_num)
    log_v_18.2 (by convert! log_c_18.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_19 : (36049961 / 8000000) ≤ -Real.log (54263 / 4915200) ∧
    -Real.log (54263 / 4915200) ≤ (1126561283 / 250000000) := by
  have h := checkLog_sound (w := (22537 / 131063)) (n := 12)
    (lo := (69472409 / 200000000)) (hi := (173681023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 54263) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 54263) = 1/(54263 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_19 : (5550613 / 500000000) ≤ -Real.log (4860937 / 4915200) ∧
    -Real.log (4860937 / 4915200) ≤ (11101227 / 1000000000) := by
  have h := checkLog_sound (w := (54263 / 9776137)) (n := 12)
    (lo := (5550613 / 500000000)) (hi := (11101227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4860937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4860937) = 1/(4860937 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_19 : (2247571949 / 1000000000) ≤ xi (54263 / 4915200) ∧ xi (54263 / 4915200) ≤ (2247571953 / 1000000000) ∧
    (4517346351 / 2000000000) ≤ kap (54263 / 4915200) ∧ kap (54263 / 4915200) ≤ (4517346359 / 2000000000) := by
  have h := endpoint_bounds (v := ((54263 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_19.1 (by convert! log_c_19.1 using 1; norm_num)
    log_v_19.2 (by convert! log_c_19.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_20 : (2250650017 / 500000000) ≤ -Real.log (13633 / 1228800) ∧
    -Real.log (13633 / 1228800) ≤ (4501300041 / 1000000000) := by
  have h := checkLog_sound (w := (5567 / 32833)) (n := 12)
    (lo := (171208477 / 500000000)) (hi := (68483391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 13633) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19200 / 13633) = 1/(13633 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_20 : (11156567 / 1000000000) ≤ -Real.log (1215167 / 1228800) ∧
    -Real.log (1215167 / 1228800) ≤ (1394571 / 125000000) := by
  have h := checkLog_sound (w := (13633 / 2443967)) (n := 12)
    (lo := (11156567 / 1000000000)) (hi := (1394571 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1215167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1215167) = 1/(1215167 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_20 : (2245071733 / 1000000000) ≤ xi (13633 / 1228800) ∧ xi (13633 / 1228800) ≤ (2245071737 / 1000000000) ∧
    (4512456601 / 2000000000) ≤ kap (13633 / 1228800) ∧ kap (13633 / 1228800) ≤ (4512456609 / 2000000000) := by
  have h := endpoint_bounds (v := ((13633 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_20.1 (by convert! log_c_20.1 using 1; norm_num)
    log_v_20.2 (by convert! log_c_20.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_21 : (2248189639 / 500000000) ≤ -Real.log (18267 / 1638400) ∧
    -Real.log (18267 / 1638400) ≤ (899275857 / 200000000) := by
  have h := checkLog_sound (w := (7333 / 43867)) (n := 12)
    (lo := (168748099 / 500000000)) (hi := (337496199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 18267) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25600 / 18267) = 1/(18267 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_21 : (11211911 / 1000000000) ≤ -Real.log (1620133 / 1638400) ∧
    -Real.log (1620133 / 1638400) ≤ (1401489 / 125000000) := by
  have h := checkLog_sound (w := (18267 / 3258533)) (n := 12)
    (lo := (11211911 / 1000000000)) (hi := (1401489 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638400 / 1620133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638400 / 1620133) = 1/(1620133 / 1638400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_21 : (2242583683 / 1000000000) ≤ xi (18267 / 1638400) ∧ xi (18267 / 1638400) ≤ (2242583687 / 1000000000) ∧
    (4507591189 / 2000000000) ≤ kap (18267 / 1638400) ∧ kap (18267 / 1638400) ≤ (4507591197 / 2000000000) := by
  have h := endpoint_bounds (v := ((18267 / 1638400) : ℝ)) (by norm_num) (by norm_num)
    log_v_21.1 (by convert! log_c_21.1 using 1; norm_num)
    log_v_21.2 (by convert! log_c_21.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_22 : (561435327 / 125000000) ≤ -Real.log (5507 / 491520) ∧
    -Real.log (5507 / 491520) ≤ (4491482623 / 1000000000) := by
  have h := checkLog_sound (w := (2173 / 13187)) (n := 12)
    (lo := (20787471 / 62500000)) (hi := (332599537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 5507) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7680 / 5507) = 1/(5507 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_22 : (5633629 / 500000000) ≤ -Real.log (486013 / 491520) ∧
    -Real.log (486013 / 491520) ≤ (11267259 / 1000000000) := by
  have h := checkLog_sound (w := (5507 / 977533)) (n := 12)
    (lo := (5633629 / 500000000)) (hi := (11267259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491520 / 486013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491520 / 486013) = 1/(486013 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_22 : (4480215357 / 2000000000) ≤ xi (5507 / 491520) ∧ xi (5507 / 491520) ≤ (896043073 / 400000000) ∧
    (2251374937 / 1000000000) ≤ kap (5507 / 491520) ∧ kap (5507 / 491520) ≤ (2251374941 / 1000000000) := by
  have h := endpoint_bounds (v := ((5507 / 491520) : ℝ)) (by norm_num) (by norm_num)
    log_v_22.1 (by convert! log_c_22.1 using 1; norm_num)
    log_v_22.2 (by convert! log_c_22.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_23 : (560826227 / 125000000) ≤ -Real.log (55339 / 4915200) ∧
    -Real.log (55339 / 4915200) ≤ (4486609823 / 1000000000) := by
  have h := checkLog_sound (w := (21461 / 132139)) (n := 12)
    (lo := (20482921 / 62500000)) (hi := (327726737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 55339) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 55339) = 1/(55339 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_23 : (11322607 / 1000000000) ≤ -Real.log (4859861 / 4915200) ∧
    -Real.log (4859861 / 4915200) ≤ (707663 / 62500000) := by
  have h := checkLog_sound (w := (55339 / 9775061)) (n := 12)
    (lo := (11322607 / 1000000000)) (hi := (707663 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4859861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4859861) = 1/(4859861 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_23 : (559410901 / 250000000) ≤ xi (55339 / 4915200) ∧ xi (55339 / 4915200) ≤ (279705451 / 125000000) ∧
    (4497932423 / 2000000000) ≤ kap (55339 / 4915200) ∧ kap (55339 / 4915200) ≤ (4497932431 / 2000000000) := by
  have h := endpoint_bounds (v := ((55339 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_23.1 (by convert! log_c_23.1 using 1; norm_num)
    log_v_23.2 (by convert! log_c_23.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_24 : (1120440161 / 250000000) ≤ -Real.log (2317 / 204800) ∧
    -Real.log (2317 / 204800) ≤ (4481760651 / 1000000000) := by
  have h := checkLog_sound (w := (883 / 5517)) (n := 12)
    (lo := (80719391 / 250000000)) (hi := (64575513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2317) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3200 / 2317) = 1/(2317 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_24 : (284449 / 25000000) ≤ -Real.log (202483 / 204800) ∧
    -Real.log (202483 / 204800) ≤ (11377961 / 1000000000) := by
  have h := checkLog_sound (w := (2317 / 407283)) (n := 12)
    (lo := (284449 / 25000000)) (hi := (11377961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 202483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 202483) = 1/(202483 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_24 : (4470382683 / 2000000000) ≤ xi (2317 / 204800) ∧ xi (2317 / 204800) ≤ (4470382691 / 2000000000) ∧
    (1123284651 / 500000000) ≤ kap (2317 / 204800) ∧ kap (2317 / 204800) ≤ (1123284653 / 500000000) := by
  have h := endpoint_bounds (v := ((2317 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_24.1 (by convert! log_c_24.1 using 1; norm_num)
    log_v_24.2 (by convert! log_c_24.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_25 : (4476934873 / 1000000000) ≤ -Real.log (55877 / 4915200) ∧
    -Real.log (55877 / 4915200) ≤ (27980843 / 6250000) := by
  have h := checkLog_sound (w := (20923 / 132677)) (n := 12)
    (lo := (318051793 / 1000000000)) (hi := (159025897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 55877) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 55877) = 1/(55877 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_25 : (2858329 / 250000000) ≤ -Real.log (4859323 / 4915200) ∧
    -Real.log (4859323 / 4915200) ≤ (11433317 / 1000000000) := by
  have h := checkLog_sound (w := (55877 / 9774523)) (n := 12)
    (lo := (2858329 / 250000000)) (hi := (11433317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4859323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4859323) = 1/(4859323 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_25 : (1116375389 / 500000000) ≤ xi (55877 / 4915200) ∧ xi (55877 / 4915200) ≤ (1116375391 / 500000000) ∧
    (4488368189 / 2000000000) ≤ kap (55877 / 4915200) ∧ kap (55877 / 4915200) ≤ (4488368197 / 2000000000) := by
  have h := endpoint_bounds (v := ((55877 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_25.1 (by convert! log_c_25.1 using 1; norm_num)
    log_v_25.2 (by convert! log_c_25.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_26 : (4472132279 / 1000000000) ≤ -Real.log (28073 / 2457600) ∧
    -Real.log (28073 / 2457600) ≤ (2236066143 / 500000000) := by
  have h := checkLog_sound (w := (10327 / 66473)) (n := 12)
    (lo := (313249199 / 1000000000)) (hi := (783123 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 28073) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 28073) = 1/(28073 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_26 : (459547 / 40000000) ≤ -Real.log (2429527 / 2457600) ∧
    -Real.log (2429527 / 2457600) ≤ (2872169 / 250000000) := by
  have h := checkLog_sound (w := (28073 / 4887127)) (n := 12)
    (lo := (459547 / 40000000)) (hi := (2872169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2429527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2429527) = 1/(2429527 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_26 : (4460643603 / 2000000000) ≤ xi (28073 / 2457600) ∧ xi (28073 / 2457600) ≤ (4460643611 / 2000000000) ∧
    (2241810477 / 1000000000) ≤ kap (28073 / 2457600) ∧ kap (28073 / 2457600) ≤ (2241810481 / 1000000000) := by
  have h := endpoint_bounds (v := ((28073 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_26.1 (by convert! log_c_26.1 using 1; norm_num)
    log_v_26.2 (by convert! log_c_26.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_27 : (4467352639 / 1000000000) ≤ -Real.log (3761 / 327680) ∧
    -Real.log (3761 / 327680) ≤ (2233676323 / 500000000) := by
  have h := checkLog_sound (w := (1359 / 8881)) (n := 12)
    (lo := (308469559 / 1000000000)) (hi := (7711739 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3761) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5120 / 3761) = 1/(3761 / 327680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_27 : (11544037 / 1000000000) ≤ -Real.log (323919 / 327680) ∧
    -Real.log (323919 / 327680) ≤ (5772019 / 500000000) := by
  have h := checkLog_sound (w := (3761 / 651599)) (n := 12)
    (lo := (11544037 / 1000000000)) (hi := (5772019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327680 / 323919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327680 / 323919) = 1/(323919 / 327680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_27 : (4455808601 / 2000000000) ≤ xi (3761 / 327680) ∧ xi (3761 / 327680) ≤ (4455808609 / 2000000000) ∧
    (1119724169 / 500000000) ≤ kap (3761 / 327680) ∧ kap (3761 / 327680) ≤ (1119724171 / 500000000) := by
  have h := endpoint_bounds (v := ((3761 / 327680) : ℝ)) (by norm_num) (by norm_num)
    log_v_27.1 (by convert! log_c_27.1 using 1; norm_num)
    log_v_27.2 (by convert! log_c_27.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_28 : (557824467 / 125000000) ≤ -Real.log (14171 / 1228800) ∧
    -Real.log (14171 / 1228800) ≤ (4462595743 / 1000000000) := by
  have h := checkLog_sound (w := (5029 / 33371)) (n := 12)
    (lo := (18982041 / 62500000)) (hi := (303712657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 14171) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19200 / 14171) = 1/(14171 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_28 : (11599403 / 1000000000) ≤ -Real.log (1214629 / 1228800) ∧
    -Real.log (1214629 / 1228800) ≤ (2899851 / 250000000) := by
  have h := checkLog_sound (w := (14171 / 2443429)) (n := 12)
    (lo := (11599403 / 1000000000)) (hi := (2899851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1214629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1214629) = 1/(1214629 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_28 : (1112749083 / 500000000) ≤ xi (14171 / 1228800) ∧ xi (14171 / 1228800) ≤ (222549817 / 100000000) ∧
    (4474195139 / 2000000000) ≤ kap (14171 / 1228800) ∧ kap (14171 / 1228800) ≤ (4474195147 / 2000000000) := by
  have h := endpoint_bounds (v := ((14171 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_28.1 (by convert! log_c_28.1 using 1; norm_num)
    log_v_28.2 (by convert! log_c_28.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_29 : (4457861353 / 1000000000) ≤ -Real.log (56953 / 4915200) ∧
    -Real.log (56953 / 4915200) ≤ (55723267 / 12500000) := by
  have h := checkLog_sound (w := (19847 / 133753)) (n := 12)
    (lo := (298978273 / 1000000000)) (hi := (149489137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 56953) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(76800 / 56953) = 1/(56953 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_29 : (11654771 / 1000000000) ≤ -Real.log (4858247 / 4915200) ∧
    -Real.log (4858247 / 4915200) ≤ (2913693 / 250000000) := by
  have h := checkLog_sound (w := (56953 / 9773447)) (n := 12)
    (lo := (11654771 / 1000000000)) (hi := (2913693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4915200 / 4858247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4915200 / 4858247) = 1/(4858247 / 4915200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_29 : (4446206581 / 2000000000) ≤ xi (56953 / 4915200) ∧ xi (56953 / 4915200) ≤ (4446206589 / 2000000000) ∧
    (1117379031 / 500000000) ≤ kap (56953 / 4915200) ∧ kap (56953 / 4915200) ≤ (1117379033 / 500000000) := by
  have h := endpoint_bounds (v := ((56953 / 4915200) : ℝ)) (by norm_num) (by norm_num)
    log_v_29.1 (by convert! log_c_29.1 using 1; norm_num)
    log_v_29.2 (by convert! log_c_29.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_30 : (27832183 / 6250000) ≤ -Real.log (9537 / 819200) ∧
    -Real.log (9537 / 819200) ≤ (4453149287 / 1000000000) := by
  have h := checkLog_sound (w := (3263 / 22337)) (n := 12)
    (lo := (1471331 / 5000000)) (hi := (294266201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 9537) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12800 / 9537) = 1/(9537 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_30 : (5855071 / 500000000) ≤ -Real.log (809663 / 819200) ∧
    -Real.log (809663 / 819200) ≤ (11710143 / 1000000000) := by
  have h := checkLog_sound (w := (9537 / 1628863)) (n := 12)
    (lo := (5855071 / 500000000)) (hi := (11710143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 809663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 809663) = 1/(809663 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_30 : (4441439137 / 2000000000) ≤ xi (9537 / 819200) ∧ xi (9537 / 819200) ≤ (888287829 / 400000000) ∧
    (2232429711 / 1000000000) ≤ kap (9537 / 819200) ∧ kap (9537 / 819200) ≤ (446485943 / 200000000) := by
  have h := endpoint_bounds (v := ((9537 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_30.1 (by convert! log_c_30.1 using 1; norm_num)
    log_v_30.2 (by convert! log_c_30.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_31 : (177751649 / 40000000) ≤ -Real.log (361 / 30720) ∧
    -Real.log (361 / 30720) ≤ (34717119 / 7812500) := by
  have h := checkLog_sound (w := (119 / 841)) (n := 12)
    (lo := (56981629 / 200000000)) (hi := (142454073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((480 / 361) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(480 / 361) = 1/(361 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_31 : (5910447 / 500000000) ≤ -Real.log (30359 / 30720) ∧
    -Real.log (30359 / 30720) ≤ (2364179 / 200000000) := by
  have h := checkLog_sound (w := (361 / 61079)) (n := 12)
    (lo := (5910447 / 500000000)) (hi := (2364179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30720 / 30359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30720 / 30359) = 1/(30359 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_31 : (443197033 / 200000000) ≤ xi (361 / 30720) ∧ xi (361 / 30720) ≤ (2215985169 / 1000000000) ∧
    (4455612119 / 2000000000) ≤ kap (361 / 30720) ∧ kap (361 / 30720) ≤ (4455612127 / 2000000000) := by
  have h := endpoint_bounds (v := ((361 / 30720) : ℝ)) (by norm_num) (by norm_num)
    log_v_31.1 (by convert! log_c_31.1 using 1; norm_num)
    log_v_31.2 (by convert! log_c_31.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


