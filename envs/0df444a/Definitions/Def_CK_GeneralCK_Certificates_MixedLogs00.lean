-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLogs00
-- name    : CK_GeneralCK_Certificates_MixedLogs00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:23:11.275457+00:00
-- url     : https://prove2.me/theorems/e9dd8629-7518-44ef-814c-f499fade95b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLogs00` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLogs00` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLogs00` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLogs00 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLogs00.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_v_0 : (3091042451 / 1000000000) ≤ -Real.log (1 / 22) ∧
    -Real.log (1 / 22) ≤ (386380307 / 125000000) := by
  have h := checkLog_sound (w := (3 / 19)) (n := 12)
    (lo := (318453731 / 1000000000)) (hi := (79613433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 8) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11 / 8) = 1/(1 / 22) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_0 : (9304003 / 200000000) ≤ -Real.log (21 / 22) ∧
    -Real.log (21 / 22) ≤ (2907501 / 62500000) := by
  have h := checkLog_sound (w := (1 / 43)) (n := 12)
    (lo := (9304003 / 200000000)) (hi := (2907501 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22 / 21) = 1/(21 / 22) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_1 : (3042748441 / 1000000000) ≤ -Real.log (403 / 8448) ∧
    -Real.log (403 / 8448) ≤ (1521374223 / 500000000) := by
  have h := checkLog_sound (w := (125 / 931)) (n := 12)
    (lo := (270159721 / 1000000000)) (hi := (135079861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 403) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(528 / 403) = 1/(403 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_1 : (24439473 / 500000000) ≤ -Real.log (8045 / 8448) ∧
    -Real.log (8045 / 8448) ≤ (48878947 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 16493)) (n := 12)
    (lo := (24439473 / 500000000)) (hi := (48878947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 8045) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 8045) = 1/(8045 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_2 : (2996679689 / 1000000000) ≤ -Real.log (211 / 4224) ∧
    -Real.log (211 / 4224) ≤ (1498339847 / 500000000) := by
  have h := checkLog_sound (w := (53 / 475)) (n := 12)
    (lo := (224090969 / 1000000000)) (hi := (22409097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264 / 211) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(264 / 211) = 1/(211 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_2 : (10248691 / 200000000) ≤ -Real.log (4013 / 4224) ∧
    -Real.log (4013 / 4224) ≤ (800679 / 15625000) := by
  have h := checkLog_sound (w := (211 / 8237)) (n := 12)
    (lo := (10248691 / 200000000)) (hi := (800679 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 4013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 4013) = 1/(4013 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_3 : (23067501 / 7812500) ≤ -Real.log (147 / 2816) ∧
    -Real.log (147 / 2816) ≤ (2952640133 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 323)) (n := 12)
    (lo := (11253213 / 62500000)) (hi := (180051409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 147) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(176 / 147) = 1/(147 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_3 : (53613567 / 1000000000) ≤ -Real.log (2669 / 2816) ∧
    -Real.log (2669 / 2816) ≤ (104714 / 1953125) := by
  have h := checkLog_sound (w := (147 / 5485)) (n := 12)
    (lo := (53613567 / 1000000000)) (hi := (104714 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2669) = 1/(2669 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_4 : (1455229257 / 500000000) ≤ -Real.log (115 / 2112) ∧
    -Real.log (115 / 2112) ≤ (2910458519 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 247)) (n := 12)
    (lo := (68934897 / 500000000)) (hi := (27573959 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132 / 115) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(132 / 115) = 1/(115 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_4 : (55989311 / 1000000000) ≤ -Real.log (1997 / 2112) ∧
    -Real.log (1997 / 2112) ≤ (874833 / 15625000) := by
  have h := checkLog_sound (w := (115 / 4109)) (n := 12)
    (lo := (55989311 / 1000000000)) (hi := (874833 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1997) = 1/(1997 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_5 : (1434992203 / 500000000) ≤ -Real.log (479 / 8448) ∧
    -Real.log (479 / 8448) ≤ (2869984411 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 1007)) (n := 12)
    (lo := (48697843 / 500000000)) (hi := (97395687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 479) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(528 / 479) = 1/(479 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_5 : (7296339 / 125000000) ≤ -Real.log (7969 / 8448) ∧
    -Real.log (7969 / 8448) ≤ (58370713 / 1000000000) := by
  have h := checkLog_sound (w := (479 / 16417)) (n := 12)
    (lo := (7296339 / 125000000)) (hi := (58370713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7969) = 1/(7969 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_6 : (1415542463 / 500000000) ≤ -Real.log (83 / 1408) ∧
    -Real.log (83 / 1408) ≤ (2831084931 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 171)) (n := 12)
    (lo := (29248103 / 500000000)) (hi := (58496207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88 / 83) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(88 / 83) = 1/(83 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_6 : (30378899 / 500000000) ≤ -Real.log (1325 / 1408) ∧
    -Real.log (1325 / 1408) ≤ (60757799 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 2733)) (n := 12)
    (lo := (30378899 / 500000000)) (hi := (60757799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1325) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1325) = 1/(1325 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_7 : (2793642129 / 1000000000) ≤ -Real.log (47 / 768) ∧
    -Real.log (47 / 768) ≤ (1396821067 / 500000000) := by
  have h := checkLog_sound (w := (1 / 95)) (n := 12)
    (lo := (21053409 / 1000000000)) (hi := (2105341 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48 / 47) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(48 / 47) = 1/(47 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_7 : (12630119 / 200000000) ≤ -Real.log (721 / 768) ∧
    -Real.log (721 / 768) ≤ (15787649 / 250000000) := by
  have h := checkLog_sound (w := (47 / 1489)) (n := 12)
    (lo := (12630119 / 200000000)) (hi := (15787649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768 / 721) = 1/(721 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_8 : (2757550843 / 1000000000) ≤ -Real.log (67 / 1056) ∧
    -Real.log (67 / 1056) ≤ (2757550847 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 199)) (n := 12)
    (lo := (678109303 / 1000000000)) (hi := (84763663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132 / 67) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(132 / 67) = 1/(67 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_8 : (16387283 / 250000000) ≤ -Real.log (989 / 1056) ∧
    -Real.log (989 / 1056) ≤ (65549133 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 2045)) (n := 12)
    (lo := (16387283 / 250000000)) (hi := (65549133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1056 / 989) = 1/(989 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_9 : (272271689 / 100000000) ≤ -Real.log (185 / 2816) ∧
    -Real.log (185 / 2816) ≤ (1361358447 / 500000000) := by
  have h := checkLog_sound (w := (167 / 537)) (n := 12)
    (lo := (12865507 / 20000000)) (hi := (643275351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 185) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(352 / 185) = 1/(185 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_9 : (16988359 / 250000000) ≤ -Real.log (2631 / 2816) ∧
    -Real.log (2631 / 2816) ≤ (67953437 / 1000000000) := by
  have h := checkLog_sound (w := (185 / 5447)) (n := 12)
    (lo := (16988359 / 250000000)) (hi := (67953437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2631) = 1/(2631 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_10 : (2689055607 / 1000000000) ≤ -Real.log (287 / 4224) ∧
    -Real.log (287 / 4224) ≤ (2689055611 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 815)) (n := 12)
    (lo := (609614067 / 1000000000)) (hi := (152403517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 287) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(528 / 287) = 1/(287 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_10 : (35181767 / 500000000) ≤ -Real.log (3937 / 4224) ∧
    -Real.log (3937 / 4224) ≤ (14072707 / 200000000) := by
  have h := checkLog_sound (w := (287 / 8161)) (n := 12)
    (lo := (35181767 / 500000000)) (hi := (14072707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3937) = 1/(3937 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_11 : (531298121 / 200000000) ≤ -Real.log (593 / 8448) ∧
    -Real.log (593 / 8448) ≤ (2656490609 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1649)) (n := 12)
    (lo := (115409813 / 200000000)) (hi := (288524533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 593) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 593) = 1/(593 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_11 : (14555891 / 200000000) ≤ -Real.log (7855 / 8448) ∧
    -Real.log (7855 / 8448) ≤ (1137179 / 15625000) := by
  have h := checkLog_sound (w := (593 / 16303)) (n := 12)
    (lo := (14555891 / 200000000)) (hi := (1137179 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7855) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7855) = 1/(7855 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_12 : (2624952721 / 1000000000) ≤ -Real.log (51 / 704) ∧
    -Real.log (51 / 704) ≤ (104998109 / 40000000) := by
  have h := checkLog_sound (w := (37 / 139)) (n := 12)
    (lo := (545511181 / 1000000000)) (hi := (272755591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(88 / 51) = 1/(51 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_12 : (37600613 / 500000000) ≤ -Real.log (653 / 704) ∧
    -Real.log (653 / 704) ≤ (75201227 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 1357)) (n := 12)
    (lo := (37600613 / 500000000)) (hi := (75201227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704 / 653) = 1/(653 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_13 : (2594379141 / 1000000000) ≤ -Real.log (631 / 8448) ∧
    -Real.log (631 / 8448) ≤ (518875829 / 200000000) := by
  have h := checkLog_sound (w := (425 / 1687)) (n := 12)
    (lo := (514937601 / 1000000000)) (hi := (257468801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 631) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1056 / 631) = 1/(631 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_13 : (77628877 / 1000000000) ≤ -Real.log (7817 / 8448) ∧
    -Real.log (7817 / 8448) ≤ (38814439 / 500000000) := by
  have h := checkLog_sound (w := (631 / 16265)) (n := 12)
    (lo := (77628877 / 1000000000)) (hi := (38814439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7817) = 1/(7817 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_14 : (2564712641 / 1000000000) ≤ -Real.log (325 / 4224) ∧
    -Real.log (325 / 4224) ≤ (512942529 / 200000000) := by
  have h := checkLog_sound (w := (203 / 853)) (n := 12)
    (lo := (485271101 / 1000000000)) (hi := (242635551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 325) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(528 / 325) = 1/(325 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_14 : (20015609 / 250000000) ≤ -Real.log (3899 / 4224) ∧
    -Real.log (3899 / 4224) ≤ (80062437 / 1000000000) := by
  have h := checkLog_sound (w := (325 / 8123)) (n := 12)
    (lo := (20015609 / 250000000)) (hi := (80062437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3899) = 1/(3899 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_15 : (158493809 / 62500000) ≤ -Real.log (223 / 2816) ∧
    -Real.log (223 / 2816) ≤ (633975237 / 250000000) := by
  have h := checkLog_sound (w := (129 / 575)) (n := 12)
    (lo := (114114851 / 250000000)) (hi := (91291881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 223) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(352 / 223) = 1/(223 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_15 : (82501931 / 1000000000) ≤ -Real.log (2593 / 2816) ∧
    -Real.log (2593 / 2816) ≤ (20625483 / 250000000) := by
  have h := checkLog_sound (w := (223 / 5409)) (n := 12)
    (lo := (82501931 / 1000000000)) (hi := (20625483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2593) = 1/(2593 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

end GeneralCK.Certificates.Mixed


