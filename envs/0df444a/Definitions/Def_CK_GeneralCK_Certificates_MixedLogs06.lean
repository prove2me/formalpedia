-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLogs06
-- name    : CK_GeneralCK_Certificates_MixedLogs06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:25:29.390617+00:00
-- url     : https://prove2.me/theorems/7f174188-7b6f-4cad-898e-1fc0f201df41
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLogs06` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLogs06` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLogs06` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLogs06 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLogs06.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_v_96 : (1291500843 / 1000000000) ≤ -Real.log (387 / 1408) ∧
    -Real.log (387 / 1408) ≤ (258300169 / 200000000) := by
  have h := checkLog_sound (w := (317 / 1091)) (n := 12)
    (lo := (598353663 / 1000000000)) (hi := (2337319 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 387) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(704 / 387) = 1/(387 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_96 : (160693859 / 500000000) ≤ -Real.log (1021 / 1408) ∧
    -Real.log (1021 / 1408) ≤ (321387719 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 2429)) (n := 12)
    (lo := (160693859 / 500000000)) (hi := (321387719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1021) = 1/(1021 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_97 : (1275268107 / 1000000000) ≤ -Real.log (295 / 1056) ∧
    -Real.log (295 / 1056) ≤ (1275268109 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 823)) (n := 12)
    (lo := (582120927 / 1000000000)) (hi := (18191279 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 295) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(528 / 295) = 1/(295 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_97 : (163805053 / 500000000) ≤ -Real.log (761 / 1056) ∧
    -Real.log (761 / 1056) ≤ (327610107 / 1000000000) := by
  have h := checkLog_sound (w := (295 / 1817)) (n := 12)
    (lo := (163805053 / 500000000)) (hi := (327610107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1056 / 761) = 1/(761 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_98 : (1259294669 / 1000000000) ≤ -Real.log (109 / 384) ∧
    -Real.log (109 / 384) ≤ (1259294671 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 301)) (n := 12)
    (lo := (566147489 / 1000000000)) (hi := (56614749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 109) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(192 / 109) = 1/(109 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_98 : (166935727 / 500000000) ≤ -Real.log (275 / 384) ∧
    -Real.log (275 / 384) ≤ (66774291 / 200000000) := by
  have h := checkLog_sound (w := (109 / 659)) (n := 12)
    (lo := (166935727 / 500000000)) (hi := (66774291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 275) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384 / 275) = 1/(275 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_99 : (155446547 / 125000000) ≤ -Real.log (203 / 704) ∧
    -Real.log (203 / 704) ≤ (621786189 / 500000000) := by
  have h := checkLog_sound (w := (149 / 555)) (n := 12)
    (lo := (137606299 / 250000000)) (hi := (550425197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(352 / 203) = 1/(203 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_99 : (68034451 / 200000000) ≤ -Real.log (501 / 704) ∧
    -Real.log (501 / 704) ≤ (10630383 / 31250000) := by
  have h := checkLog_sound (w := (203 / 1205)) (n := 12)
    (lo := (68034451 / 200000000)) (hi := (10630383 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704 / 501) = 1/(501 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_100 : (307023363 / 250000000) ≤ -Real.log (1237 / 4224) ∧
    -Real.log (1237 / 4224) ≤ (614046727 / 500000000) := by
  have h := checkLog_sound (w := (875 / 3349)) (n := 12)
    (lo := (16717071 / 31250000)) (hi := (534946273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2112 / 1237) = 1/(1237 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_100 : (346513007 / 1000000000) ≤ -Real.log (2987 / 4224) ∧
    -Real.log (2987 / 4224) ≤ (21657063 / 62500000) := by
  have h := checkLog_sound (w := (1237 / 7211)) (n := 12)
    (lo := (346513007 / 1000000000)) (hi := (21657063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 2987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 2987) = 1/(2987 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_101 : (1212850477 / 1000000000) ≤ -Real.log (157 / 528) ∧
    -Real.log (157 / 528) ≤ (1212850479 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 421)) (n := 12)
    (lo := (519703297 / 1000000000)) (hi := (259851649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264 / 157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(264 / 157) = 1/(157 / 528) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_101 : (352894221 / 1000000000) ≤ -Real.log (371 / 528) ∧
    -Real.log (371 / 528) ≤ (176447111 / 500000000) := by
  have h := checkLog_sound (w := (157 / 899)) (n := 12)
    (lo := (352894221 / 1000000000)) (hi := (176447111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(528 / 371) = 1/(371 / 528) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_102 : (1183044349 / 1000000000) ≤ -Real.log (647 / 2112) ∧
    -Real.log (647 / 2112) ≤ (1183044351 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 1703)) (n := 12)
    (lo := (489897169 / 1000000000)) (hi := (48989717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056 / 647) = 1/(647 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_102 : (365780123 / 1000000000) ≤ -Real.log (1465 / 2112) ∧
    -Real.log (1465 / 2112) ≤ (91445031 / 250000000) := by
  have h := checkLog_sound (w := (647 / 3577)) (n := 12)
    (lo := (365780123 / 1000000000)) (hi := (91445031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1465) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1465) = 1/(1465 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_103 : (1154100973 / 1000000000) ≤ -Real.log (111 / 352) ∧
    -Real.log (111 / 352) ≤ (46164039 / 40000000) := by
  have h := checkLog_sound (w := (65 / 287)) (n := 12)
    (lo := (460953793 / 1000000000)) (hi := (230476897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(176 / 111) = 1/(111 / 352) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_103 : (189417121 / 500000000) ≤ -Real.log (241 / 352) ∧
    -Real.log (241 / 352) ≤ (378834243 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 593)) (n := 12)
    (lo := (189417121 / 500000000)) (hi := (378834243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352 / 241) = 1/(241 / 352) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_104 : (562985903 / 500000000) ≤ -Real.log (685 / 2112) ∧
    -Real.log (685 / 2112) ≤ (35186619 / 31250000) := by
  have h := checkLog_sound (w := (371 / 1741)) (n := 12)
    (lo := (216412313 / 500000000)) (hi := (432824627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 685) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056 / 685) = 1/(685 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_104 : (392061027 / 1000000000) ≤ -Real.log (1427 / 2112) ∧
    -Real.log (1427 / 2112) ≤ (98015257 / 250000000) := by
  have h := checkLog_sound (w := (685 / 3539)) (n := 12)
    (lo := (392061027 / 1000000000)) (hi := (98015257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1427) = 1/(1427 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_105 : (17165817 / 15625000) ≤ -Real.log (1 / 3) ∧
    -Real.log (1 / 3) ≤ (109861229 / 100000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3 / 2) = 1/(1 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_105 : (101366277 / 250000000) ≤ -Real.log (2 / 3) ∧
    -Real.log (2 / 3) ≤ (405465109 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3 / 2) = 1/(2 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

end GeneralCK.Certificates.Mixed


