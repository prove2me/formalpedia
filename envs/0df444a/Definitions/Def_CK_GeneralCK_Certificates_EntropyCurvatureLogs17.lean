-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs17
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:43:17.181544+00:00
-- url     : https://prove2.me/theorems/c7839d46-ebc2-4fe8-9abc-8d25f47efa55
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs17` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs17` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs17` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs17 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs17.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_272 : (191017411 / 200000000) ≤ -Real.log (29551 / 76800) ∧
    -Real.log (29551 / 76800) ≤ (955087057 / 1000000000) := by
  have h := checkLog_sound (w := (8849 / 67951)) (n := 12)
    (lo := (2095519 / 8000000)) (hi := (65484969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 29551) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38400 / 29551) = 1/(29551 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_272 : (9715463 / 20000000) ≤ -Real.log (47249 / 76800) ∧
    -Real.log (47249 / 76800) ≤ (485773151 / 1000000000) := by
  have h := checkLog_sound (w := (29551 / 124049)) (n := 12)
    (lo := (9715463 / 20000000)) (hi := (485773151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 47249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 47249) = 1/(47249 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_272 : (29332119 / 125000000) ≤ xi (29551 / 76800) ∧ xi (29551 / 76800) ≤ (469313907 / 2000000000) ∧
    (288172041 / 400000000) ≤ kap (29551 / 76800) ∧ kap (29551 / 76800) ≤ (90053763 / 125000000) := by
  have h := endpoint_bounds (v := ((29551 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_272.1 (by convert! log_c_272.1 using 1; norm_num)
    log_v_272.2 (by convert! log_c_272.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_273 : (94602533 / 100000000) ≤ -Real.log (497 / 1280) ∧
    -Real.log (497 / 1280) ≤ (236506333 / 250000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 497) = 1/(497 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_273 : (24574133 / 50000000) ≤ -Real.log (783 / 1280) ∧
    -Real.log (783 / 1280) ≤ (491482661 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 2063)) (n := 12)
    (lo := (24574133 / 50000000)) (hi := (491482661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 783) = 1/(783 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_273 : (454542669 / 2000000000) ≤ xi (497 / 1280) ∧ xi (497 / 1280) ≤ (28408917 / 125000000) ∧
    (143750799 / 200000000) ≤ kap (497 / 1280) ∧ kap (497 / 1280) ≤ (1437507993 / 2000000000) := by
  have h := endpoint_bounds (v := ((497 / 1280) : ℝ)) (by norm_num) (by norm_num)
    log_v_273.1 (by convert! log_c_273.1 using 1; norm_num)
    log_v_273.2 (by convert! log_c_273.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_274 : (937044983 / 1000000000) ≤ -Real.log (30089 / 76800) ∧
    -Real.log (30089 / 76800) ≤ (187408997 / 200000000) := by
  have h := checkLog_sound (w := (8311 / 68489)) (n := 12)
    (lo := (243897803 / 1000000000)) (hi := (60974451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 30089) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38400 / 30089) = 1/(30089 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_274 : (497224957 / 1000000000) ≤ -Real.log (46711 / 76800) ∧
    -Real.log (46711 / 76800) ≤ (248612479 / 500000000) := by
  have h := checkLog_sound (w := (30089 / 123511)) (n := 12)
    (lo := (497224957 / 1000000000)) (hi := (248612479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 46711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 46711) = 1/(46711 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_274 : (17592801 / 80000000) ≤ xi (30089 / 76800) ∧ xi (30089 / 76800) ≤ (109955007 / 500000000) ∧
    (71713497 / 100000000) ≤ kap (30089 / 76800) ∧ kap (30089 / 76800) ≤ (1434269943 / 2000000000) := by
  have h := endpoint_bounds (v := ((30089 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_274.1 (by convert! log_c_274.1 using 1; norm_num)
    log_v_274.2 (by convert! log_c_274.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_275 : (185628913 / 200000000) ≤ -Real.log (15179 / 38400) ∧
    -Real.log (15179 / 38400) ≤ (928144567 / 1000000000) := by
  have h := checkLog_sound (w := (4021 / 34379)) (n := 12)
    (lo := (46999477 / 200000000)) (hi := (117498693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 15179) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 15179) = 1/(15179 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_275 : (503000417 / 1000000000) ≤ -Real.log (23221 / 38400) ∧
    -Real.log (23221 / 38400) ≤ (251500209 / 500000000) := by
  have h := checkLog_sound (w := (15179 / 61621)) (n := 12)
    (lo := (503000417 / 1000000000)) (hi := (251500209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 23221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 23221) = 1/(23221 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_275 : (425144147 / 2000000000) ≤ xi (15179 / 38400) ∧ xi (15179 / 38400) ≤ (8502883 / 40000000) ∧
    (715572491 / 1000000000) ≤ kap (15179 / 38400) ∧ kap (15179 / 38400) ≤ (286228997 / 400000000) := by
  have h := endpoint_bounds (v := ((15179 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_275.1 (by convert! log_c_275.1 using 1; norm_num)
    log_v_275.2 (by convert! log_c_275.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_276 : (459661333 / 500000000) ≤ -Real.log (10209 / 25600) ∧
    -Real.log (10209 / 25600) ≤ (229830667 / 250000000) := by
  have h := checkLog_sound (w := (2591 / 23009)) (n := 12)
    (lo := (113087743 / 500000000)) (hi := (226175487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 10209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12800 / 10209) = 1/(10209 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_276 : (127202357 / 250000000) ≤ -Real.log (15391 / 25600) ∧
    -Real.log (15391 / 25600) ≤ (508809429 / 1000000000) := by
  have h := checkLog_sound (w := (10209 / 40991)) (n := 12)
    (lo := (127202357 / 250000000)) (hi := (508809429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 15391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 15391) = 1/(15391 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_276 : (410513237 / 2000000000) ≤ xi (10209 / 25600) ∧ xi (10209 / 25600) ≤ (10262831 / 50000000) ∧
    (714066047 / 1000000000) ≤ kap (10209 / 25600) ∧ kap (10209 / 25600) ≤ (1428132097 / 2000000000) := by
  have h := endpoint_bounds (v := ((10209 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_276.1 (by convert! log_c_276.1 using 1; norm_num)
    log_v_276.2 (by convert! log_c_276.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_277 : (910577913 / 1000000000) ≤ -Real.log (1931 / 4800) ∧
    -Real.log (1931 / 4800) ≤ (182115583 / 200000000) := by
  have h := checkLog_sound (w := (469 / 4331)) (n := 12)
    (lo := (217430733 / 1000000000)) (hi := (108715367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 1931) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2400 / 1931) = 1/(1931 / 4800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_277 : (25732619 / 50000000) ≤ -Real.log (2869 / 4800) ∧
    -Real.log (2869 / 4800) ≤ (514652381 / 1000000000) := by
  have h := checkLog_sound (w := (1931 / 7669)) (n := 12)
    (lo := (25732619 / 50000000)) (hi := (514652381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 2869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4800 / 2869) = 1/(2869 / 4800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_277 : (98981383 / 500000000) ≤ xi (1931 / 4800) ∧ xi (1931 / 4800) ≤ (79185107 / 400000000) ∧
    (1425230293 / 2000000000) ≤ kap (1931 / 4800) ∧ kap (1931 / 4800) ≤ (178153787 / 250000000) := by
  have h := endpoint_bounds (v := ((1931 / 4800) : ℝ)) (by norm_num) (by norm_num)
    log_v_277.1 (by convert! log_c_277.1 using 1; norm_num)
    log_v_277.2 (by convert! log_c_277.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_278 : (906234047 / 1000000000) ≤ -Real.log (20687 / 51200) ∧
    -Real.log (20687 / 51200) ≤ (906234049 / 1000000000) := by
  have h := checkLog_sound (w := (4913 / 46287)) (n := 12)
    (lo := (213086867 / 1000000000)) (hi := (53271717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 20687) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25600 / 20687) = 1/(20687 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_278 : (517586709 / 1000000000) ≤ -Real.log (30513 / 51200) ∧
    -Real.log (30513 / 51200) ≤ (51758671 / 100000000) := by
  have h := checkLog_sound (w := (20687 / 81713)) (n := 12)
    (lo := (517586709 / 1000000000)) (hi := (51758671 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 30513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 30513) = 1/(30513 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_278 : (388647337 / 2000000000) ≤ xi (20687 / 51200) ∧ xi (20687 / 51200) ≤ (19432367 / 100000000) ∧
    (355955189 / 500000000) ≤ kap (20687 / 51200) ∧ kap (20687 / 51200) ≤ (1423820759 / 2000000000) := by
  have h := endpoint_bounds (v := ((20687 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_278.1 (by convert! log_c_278.1 using 1; norm_num)
    log_v_278.2 (by convert! log_c_278.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_279 : (901908969 / 1000000000) ≤ -Real.log (6233 / 15360) ∧
    -Real.log (6233 / 15360) ≤ (901908971 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 13913)) (n := 12)
    (lo := (208761789 / 1000000000)) (hi := (20876179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 6233) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7680 / 6233) = 1/(6233 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_279 : (260264837 / 500000000) ≤ -Real.log (9127 / 15360) ∧
    -Real.log (9127 / 15360) ≤ (20821187 / 40000000) := by
  have h := checkLog_sound (w := (6233 / 24487)) (n := 12)
    (lo := (260264837 / 500000000)) (hi := (20821187 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 9127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15360 / 9127) = 1/(9127 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_279 : (190689647 / 1000000000) ≤ xi (6233 / 15360) ∧ xi (6233 / 15360) ≤ (381379297 / 2000000000) ∧
    (1422438643 / 2000000000) ≤ kap (6233 / 15360) ∧ kap (6233 / 15360) ≤ (711219323 / 1000000000) := by
  have h := endpoint_bounds (v := ((6233 / 15360) : ℝ)) (by norm_num) (by norm_num)
    log_v_279.1 (by convert! log_c_279.1 using 1; norm_num)
    log_v_279.2 (by convert! log_c_279.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_280 : (224400629 / 250000000) ≤ -Real.log (62599 / 153600) ∧
    -Real.log (62599 / 153600) ≤ (448801259 / 500000000) := by
  have h := checkLog_sound (w := (14201 / 139399)) (n := 12)
    (lo := (25556917 / 125000000)) (hi := (204455337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 62599) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 62599) = 1/(62599 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_280 : (20939253 / 40000000) ≤ -Real.log (91001 / 153600) ∧
    -Real.log (91001 / 153600) ≤ (261740663 / 500000000) := by
  have h := checkLog_sound (w := (62599 / 244601)) (n := 12)
    (lo := (20939253 / 40000000)) (hi := (261740663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 91001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 91001) = 1/(91001 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_280 : (37412119 / 200000000) ≤ xi (62599 / 153600) ∧ xi (62599 / 153600) ≤ (374121193 / 2000000000) ∧
    (1421083841 / 2000000000) ≤ kap (62599 / 153600) ∧ kap (62599 / 153600) ≤ (355270961 / 500000000) := by
  have h := endpoint_bounds (v := ((62599 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_280.1 (by convert! log_c_280.1 using 1; norm_num)
    log_v_280.2 (by convert! log_c_280.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_281 : (893314529 / 1000000000) ≤ -Real.log (5239 / 12800) ∧
    -Real.log (5239 / 12800) ≤ (893314531 / 1000000000) := by
  have h := checkLog_sound (w := (1161 / 11639)) (n := 12)
    (lo := (200167349 / 1000000000)) (hi := (4003347 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6400 / 5239) = 1/(5239 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_281 : (263220857 / 500000000) ≤ -Real.log (7561 / 12800) ∧
    -Real.log (7561 / 12800) ≤ (105288343 / 200000000) := by
  have h := checkLog_sound (w := (5239 / 20361)) (n := 12)
    (lo := (263220857 / 500000000)) (hi := (105288343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 7561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 7561) = 1/(7561 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_281 : (183436407 / 1000000000) ≤ xi (5239 / 12800) ∧ xi (5239 / 12800) ≤ (366872817 / 2000000000) ∧
    (1419756243 / 2000000000) ≤ kap (5239 / 12800) ∧ kap (5239 / 12800) ≤ (709878123 / 1000000000) := by
  have h := endpoint_bounds (v := ((5239 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_281.1 (by convert! log_c_281.1 using 1; norm_num)
    log_v_281.2 (by convert! log_c_281.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_282 : (889044851 / 1000000000) ≤ -Real.log (63137 / 153600) ∧
    -Real.log (63137 / 153600) ≤ (889044853 / 1000000000) := by
  have h := checkLog_sound (w := (13663 / 139937)) (n := 12)
    (lo := (195897671 / 1000000000)) (hi := (24487209 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 63137) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 63137) = 1/(63137 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_282 : (529410893 / 1000000000) ≤ -Real.log (90463 / 153600) ∧
    -Real.log (90463 / 153600) ≤ (264705447 / 500000000) := by
  have h := checkLog_sound (w := (63137 / 244063)) (n := 12)
    (lo := (529410893 / 1000000000)) (hi := (264705447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 90463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 90463) = 1/(90463 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_282 : (359633957 / 2000000000) ≤ xi (63137 / 153600) ∧ xi (63137 / 153600) ≤ (8990849 / 50000000) ∧
    (22163371 / 31250000) ≤ kap (63137 / 153600) ∧ kap (63137 / 153600) ≤ (1418455747 / 2000000000) := by
  have h := endpoint_bounds (v := ((63137 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_282.1 (by convert! log_c_282.1 using 1; norm_num)
    log_v_282.2 (by convert! log_c_282.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_283 : (35391733 / 40000000) ≤ -Real.log (31703 / 76800) ∧
    -Real.log (31703 / 76800) ≤ (884793327 / 1000000000) := by
  have h := checkLog_sound (w := (6697 / 70103)) (n := 12)
    (lo := (38329229 / 200000000)) (hi := (95823073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 31703) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38400 / 31703) = 1/(31703 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_283 : (266194457 / 500000000) ≤ -Real.log (45097 / 76800) ∧
    -Real.log (45097 / 76800) ≤ (106477783 / 200000000) := by
  have h := checkLog_sound (w := (31703 / 121897)) (n := 12)
    (lo := (266194457 / 500000000)) (hi := (106477783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 45097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 45097) = 1/(45097 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_283 : (35240441 / 200000000) ≤ xi (31703 / 76800) ∧ xi (31703 / 76800) ≤ (352404413 / 2000000000) ∧
    (1417182239 / 2000000000) ≤ kap (31703 / 76800) ∧ kap (31703 / 76800) ≤ (708591121 / 1000000000) := by
  have h := endpoint_bounds (v := ((31703 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_283.1 (by convert! log_c_283.1 using 1; norm_num)
    log_v_283.2 (by convert! log_c_283.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_284 : (880559799 / 1000000000) ≤ -Real.log (849 / 2048) ∧
    -Real.log (849 / 2048) ≤ (880559801 / 1000000000) := by
  have h := checkLog_sound (w := (175 / 1873)) (n := 12)
    (lo := (187412619 / 1000000000)) (hi := (9370631 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 849) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1024 / 849) = 1/(849 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_284 : (535375831 / 1000000000) ≤ -Real.log (1199 / 2048) ∧
    -Real.log (1199 / 2048) ≤ (66921979 / 125000000) := by
  have h := checkLog_sound (w := (849 / 3247)) (n := 12)
    (lo := (535375831 / 1000000000)) (hi := (66921979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1199) = 1/(1199 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_284 : (345183967 / 2000000000) ≤ xi (849 / 2048) ∧ xi (849 / 2048) ≤ (34518397 / 200000000) ∧
    (141593563 / 200000000) ≤ kap (849 / 2048) ∧ kap (849 / 2048) ≤ (1415935633 / 2000000000) := by
  have h := endpoint_bounds (v := ((849 / 2048) : ℝ)) (by norm_num) (by norm_num)
    log_v_284.1 (by convert! log_c_284.1 using 1; norm_num)
    log_v_284.2 (by convert! log_c_284.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_285 : (876344119 / 1000000000) ≤ -Real.log (7993 / 19200) ∧
    -Real.log (7993 / 19200) ≤ (876344121 / 1000000000) := by
  have h := checkLog_sound (w := (1607 / 17593)) (n := 12)
    (lo := (183196939 / 1000000000)) (hi := (9159847 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 7993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9600 / 7993) = 1/(7993 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_285 : (107674339 / 200000000) ≤ -Real.log (11207 / 19200) ∧
    -Real.log (11207 / 19200) ≤ (33648231 / 62500000) := by
  have h := checkLog_sound (w := (7993 / 30407)) (n := 12)
    (lo := (107674339 / 200000000)) (hi := (33648231 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 11207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 11207) = 1/(11207 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_285 : (337972423 / 2000000000) ≤ xi (7993 / 19200) ∧ xi (7993 / 19200) ≤ (168986213 / 1000000000) ∧
    (707357907 / 1000000000) ≤ kap (7993 / 19200) ∧ kap (7993 / 19200) ≤ (1414715817 / 2000000000) := by
  have h := endpoint_bounds (v := ((7993 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_285.1 (by convert! log_c_285.1 using 1; norm_num)
    log_v_285.2 (by convert! log_c_285.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_286 : (872146137 / 1000000000) ≤ -Real.log (64213 / 153600) ∧
    -Real.log (64213 / 153600) ≤ (872146139 / 1000000000) := by
  have h := checkLog_sound (w := (12587 / 141013)) (n := 12)
    (lo := (178998957 / 1000000000)) (hi := (89499479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 64213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 64213) = 1/(64213 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_286 : (270688281 / 500000000) ≤ -Real.log (89387 / 153600) ∧
    -Real.log (89387 / 153600) ≤ (541376563 / 1000000000) := by
  have h := checkLog_sound (w := (64213 / 242987)) (n := 12)
    (lo := (270688281 / 500000000)) (hi := (541376563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 89387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 89387) = 1/(89387 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_286 : (165384787 / 1000000000) ≤ xi (64213 / 153600) ∧ xi (64213 / 153600) ≤ (330769577 / 2000000000) ∧
    (1413522699 / 2000000000) ≤ kap (64213 / 153600) ∧ kap (64213 / 153600) ≤ (706761351 / 1000000000) := by
  have h := endpoint_bounds (v := ((64213 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_286.1 (by convert! log_c_286.1 using 1; norm_num)
    log_v_286.2 (by convert! log_c_286.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_287 : (173593141 / 200000000) ≤ -Real.log (10747 / 25600) ∧
    -Real.log (10747 / 25600) ≤ (867965707 / 1000000000) := by
  have h := checkLog_sound (w := (2053 / 23547)) (n := 12)
    (lo := (6992741 / 40000000)) (hi := (87409263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 10747) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12800 / 10747) = 1/(10747 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_287 : (272195243 / 500000000) ≤ -Real.log (14853 / 25600) ∧
    -Real.log (14853 / 25600) ≤ (544390487 / 1000000000) := by
  have h := checkLog_sound (w := (10747 / 40453)) (n := 12)
    (lo := (272195243 / 500000000)) (hi := (544390487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 14853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 14853) = 1/(14853 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_287 : (161787609 / 1000000000) ≤ xi (10747 / 25600) ∧ xi (10747 / 25600) ≤ (323575221 / 2000000000) ∧
    (1412356191 / 2000000000) ≤ kap (10747 / 25600) ∧ kap (10747 / 25600) ≤ (706178097 / 1000000000) := by
  have h := endpoint_bounds (v := ((10747 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_287.1 (by convert! log_c_287.1 using 1; norm_num)
    log_v_287.2 (by convert! log_c_287.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


