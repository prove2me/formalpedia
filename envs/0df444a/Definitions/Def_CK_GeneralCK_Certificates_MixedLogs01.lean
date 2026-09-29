-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLogs01
-- name    : CK_GeneralCK_Certificates_MixedLogs01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:25:40.71344+00:00
-- url     : https://prove2.me/theorems/426f6f6f-e98e-44db-bc48-ea9aca671887
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLogs01` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLogs01` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLogs01` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLogs01 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLogs01.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_v_16 : (1253948083 / 500000000) ≤ -Real.log (43 / 528) ∧
    -Real.log (43 / 528) ≤ (250789617 / 100000000) := by
  have h := checkLog_sound (w := (23 / 109)) (n := 12)
    (lo := (214227313 / 500000000)) (hi := (428454627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66 / 43) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(66 / 43) = 1/(43 / 528) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_16 : (1327303 / 15625000) ≤ -Real.log (485 / 528) ∧
    -Real.log (485 / 528) ≤ (84947393 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 1013)) (n := 12)
    (lo := (1327303 / 15625000)) (hi := (84947393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 485) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(528 / 485) = 1/(485 / 528) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_17 : (1240327169 / 500000000) ≤ -Real.log (707 / 8448) ∧
    -Real.log (707 / 8448) ≤ (1240327171 / 500000000) := by
  have h := checkLog_sound (w := (349 / 1763)) (n := 12)
    (lo := (200606399 / 500000000)) (hi := (401212799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 707) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 707) = 1/(707 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_17 : (1365607 / 15625000) ≤ -Real.log (7741 / 8448) ∧
    -Real.log (7741 / 8448) ≤ (87398849 / 1000000000) := by
  have h := checkLog_sound (w := (707 / 16189)) (n := 12)
    (lo := (1365607 / 15625000)) (hi := (87398849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7741) = 1/(7741 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_18 : (2454134989 / 1000000000) ≤ -Real.log (11 / 128) ∧
    -Real.log (11 / 128) ≤ (2454134993 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 11) = 1/(11 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_18 : (89856329 / 1000000000) ≤ -Real.log (117 / 128) ∧
    -Real.log (117 / 128) ≤ (8985633 / 100000000) := by
  have h := checkLog_sound (w := (11 / 245)) (n := 12)
    (lo := (89856329 / 1000000000)) (hi := (8985633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 117) = 1/(117 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_19 : (485660157 / 200000000) ≤ -Real.log (745 / 8448) ∧
    -Real.log (745 / 8448) ≤ (2428300789 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1801)) (n := 12)
    (lo := (69771849 / 200000000)) (hi := (174429623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 745) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 745) = 1/(745 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_19 : (92319863 / 1000000000) ≤ -Real.log (7703 / 8448) ∧
    -Real.log (7703 / 8448) ≤ (11539983 / 125000000) := by
  have h := checkLog_sound (w := (745 / 16151)) (n := 12)
    (lo := (92319863 / 1000000000)) (hi := (11539983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7703) = 1/(7703 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_20 : (480623443 / 200000000) ≤ -Real.log (191 / 2112) ∧
    -Real.log (191 / 2112) ≤ (2403117219 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 455)) (n := 12)
    (lo := (12947027 / 40000000)) (hi := (80918919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264 / 191) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(264 / 191) = 1/(191 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_20 : (47394741 / 500000000) ≤ -Real.log (1921 / 2112) ∧
    -Real.log (1921 / 2112) ≤ (94789483 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 4033)) (n := 12)
    (lo := (47394741 / 500000000)) (hi := (94789483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1921) = 1/(1921 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_21 : (594638077 / 250000000) ≤ -Real.log (261 / 2816) ∧
    -Real.log (261 / 2816) ≤ (297319039 / 125000000) := by
  have h := checkLog_sound (w := (91 / 613)) (n := 12)
    (lo := (18694423 / 62500000)) (hi := (299110769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 261) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(352 / 261) = 1/(261 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_21 : (48632607 / 500000000) ≤ -Real.log (2555 / 2816) ∧
    -Real.log (2555 / 2816) ≤ (19453043 / 200000000) := by
  have h := checkLog_sound (w := (261 / 5371)) (n := 12)
    (lo := (48632607 / 500000000)) (hi := (19453043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2555) = 1/(2555 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_22 : (588644099 / 250000000) ≤ -Real.log (401 / 4224) ∧
    -Real.log (401 / 4224) ≤ (5886441 / 2500000) := by
  have h := checkLog_sound (w := (127 / 929)) (n := 12)
    (lo := (34391857 / 125000000)) (hi := (275134857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 401) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(528 / 401) = 1/(401 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_22 : (99747091 / 1000000000) ≤ -Real.log (3823 / 4224) ∧
    -Real.log (3823 / 4224) ≤ (24936773 / 250000000) := by
  have h := checkLog_sound (w := (401 / 8047)) (n := 12)
    (lo := (99747091 / 1000000000)) (hi := (24936773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3823) = 1/(3823 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_23 : (1165580947 / 500000000) ≤ -Real.log (821 / 8448) ∧
    -Real.log (821 / 8448) ≤ (1165580949 / 500000000) := by
  have h := checkLog_sound (w := (235 / 1877)) (n := 12)
    (lo := (125860177 / 500000000)) (hi := (50344071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 821) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 821) = 1/(821 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_23 : (102235143 / 1000000000) ≤ -Real.log (7627 / 8448) ∧
    -Real.log (7627 / 8448) ≤ (12779393 / 125000000) := by
  have h := checkLog_sound (w := (821 / 16075)) (n := 12)
    (lo := (102235143 / 1000000000)) (hi := (12779393 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7627) = 1/(7627 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_24 : (288535389 / 125000000) ≤ -Real.log (35 / 352) ∧
    -Real.log (35 / 352) ≤ (577070779 / 250000000) := by
  have h := checkLog_sound (w := (9 / 79)) (n := 12)
    (lo := (57210393 / 250000000)) (hi := (228841573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44 / 35) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(44 / 35) = 1/(35 / 352) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_24 : (104729401 / 1000000000) ≤ -Real.log (317 / 352) ∧
    -Real.log (317 / 352) ≤ (52364701 / 500000000) := by
  have h := checkLog_sound (w := (35 / 669)) (n := 12)
    (lo := (104729401 / 1000000000)) (hi := (52364701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352 / 317) = 1/(317 / 352) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_25 : (1142958041 / 500000000) ≤ -Real.log (859 / 8448) ∧
    -Real.log (859 / 8448) ≤ (1142958043 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1915)) (n := 12)
    (lo := (103237271 / 500000000)) (hi := (206474543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 859) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 859) = 1/(859 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_25 : (13403737 / 125000000) ≤ -Real.log (7589 / 8448) ∧
    -Real.log (7589 / 8448) ≤ (107229897 / 1000000000) := by
  have h := checkLog_sound (w := (859 / 16037)) (n := 12)
    (lo := (13403737 / 125000000)) (hi := (107229897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7589) = 1/(7589 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_26 : (226403841 / 100000000) ≤ -Real.log (439 / 4224) ∧
    -Real.log (439 / 4224) ≤ (1132019207 / 500000000) := by
  have h := checkLog_sound (w := (89 / 967)) (n := 12)
    (lo := (18459687 / 100000000)) (hi := (184596871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 439) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(528 / 439) = 1/(439 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_26 : (109736659 / 1000000000) ≤ -Real.log (3785 / 4224) ∧
    -Real.log (3785 / 4224) ≤ (5486833 / 50000000) := by
  have h := checkLog_sound (w := (439 / 8009)) (n := 12)
    (lo := (109736659 / 1000000000)) (hi := (5486833 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3785) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3785) = 1/(3785 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_27 : (1121314571 / 500000000) ≤ -Real.log (299 / 2816) ∧
    -Real.log (299 / 2816) ≤ (1121314573 / 500000000) := by
  have h := checkLog_sound (w := (53 / 651)) (n := 12)
    (lo := (81593801 / 500000000)) (hi := (163187603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 299) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(352 / 299) = 1/(299 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_27 : (56124861 / 500000000) ≤ -Real.log (2517 / 2816) ∧
    -Real.log (2517 / 2816) ≤ (112249723 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 5333)) (n := 12)
    (lo := (56124861 / 500000000)) (hi := (112249723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2517) = 1/(2517 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_28 : (2221668639 / 1000000000) ≤ -Real.log (229 / 2112) ∧
    -Real.log (229 / 2112) ≤ (2221668643 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 493)) (n := 12)
    (lo := (142227099 / 1000000000)) (hi := (1422271 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264 / 229) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(264 / 229) = 1/(229 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_28 : (28692279 / 250000000) ≤ -Real.log (1883 / 2112) ∧
    -Real.log (1883 / 2112) ≤ (114769117 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 3995)) (n := 12)
    (lo := (28692279 / 250000000)) (hi := (114769117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1883) = 1/(1883 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_29 : (1100569237 / 500000000) ≤ -Real.log (85 / 768) ∧
    -Real.log (85 / 768) ≤ (1100569239 / 500000000) := by
  have h := checkLog_sound (w := (11 / 181)) (n := 12)
    (lo := (60848467 / 500000000)) (hi := (24339387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 85) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(96 / 85) = 1/(85 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_29 : (117294873 / 1000000000) ≤ -Real.log (683 / 768) ∧
    -Real.log (683 / 768) ≤ (58647437 / 500000000) := by
  have h := checkLog_sound (w := (85 / 1451)) (n := 12)
    (lo := (117294873 / 1000000000)) (hi := (58647437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768 / 683) = 1/(683 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_30 : (545255333 / 250000000) ≤ -Real.log (159 / 1408) ∧
    -Real.log (159 / 1408) ≤ (272627667 / 125000000) := by
  have h := checkLog_sound (w := (17 / 335)) (n := 12)
    (lo := (6348737 / 62500000)) (hi := (101579793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(176 / 159) = 1/(159 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_30 : (59913513 / 500000000) ≤ -Real.log (1249 / 1408) ∧
    -Real.log (1249 / 1408) ≤ (119827027 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 2657)) (n := 12)
    (lo := (59913513 / 500000000)) (hi := (119827027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1249) = 1/(1249 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_31 : (1080650461 / 500000000) ≤ -Real.log (973 / 8448) ∧
    -Real.log (973 / 8448) ≤ (1080650463 / 500000000) := by
  have h := checkLog_sound (w := (83 / 2029)) (n := 12)
    (lo := (40929691 / 500000000)) (hi := (81859383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 973) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 973) = 1/(973 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_31 : (122365607 / 1000000000) ≤ -Real.log (7475 / 8448) ∧
    -Real.log (7475 / 8448) ≤ (15295701 / 125000000) := by
  have h := checkLog_sound (w := (973 / 15923)) (n := 12)
    (lo := (122365607 / 1000000000)) (hi := (15295701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7475) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7475) = 1/(7475 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

end GeneralCK.Certificates.Mixed


