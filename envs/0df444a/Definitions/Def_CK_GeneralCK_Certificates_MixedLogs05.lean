-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLogs05
-- name    : CK_GeneralCK_Certificates_MixedLogs05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:22:45.860668+00:00
-- url     : https://prove2.me/theorems/c931996f-2bbe-4d7d-8fd7-32df38aa1706
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLogs05` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLogs05` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLogs05` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLogs05 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLogs05.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_v_80 : (1489972789 / 1000000000) ≤ -Real.log (119 / 528) ∧
    -Real.log (119 / 528) ≤ (186246599 / 125000000) := by
  have h := checkLog_sound (w := (13 / 251)) (n := 12)
    (lo := (103678429 / 1000000000)) (hi := (10367843 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132 / 119) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(132 / 119) = 1/(119 / 528) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_80 : (255381127 / 1000000000) ≤ -Real.log (409 / 528) ∧
    -Real.log (409 / 528) ≤ (31922641 / 125000000) := by
  have h := checkLog_sound (w := (119 / 937)) (n := 12)
    (lo := (255381127 / 1000000000)) (hi := (31922641 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(528 / 409) = 1/(409 / 528) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_81 : (1480043259 / 1000000000) ≤ -Real.log (641 / 2816) ∧
    -Real.log (641 / 2816) ≤ (740021631 / 500000000) := by
  have h := checkLog_sound (w := (63 / 1345)) (n := 12)
    (lo := (93748899 / 1000000000)) (hi := (937489 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 641) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 641) = 1/(641 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_81 : (258288773 / 1000000000) ≤ -Real.log (2175 / 2816) ∧
    -Real.log (2175 / 2816) ≤ (129144387 / 500000000) := by
  have h := checkLog_sound (w := (641 / 4991)) (n := 12)
    (lo := (258288773 / 1000000000)) (hi := (129144387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2175) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2175) = 1/(2175 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_82 : (294042271 / 200000000) ≤ -Real.log (971 / 4224) ∧
    -Real.log (971 / 4224) ≤ (735105679 / 500000000) := by
  have h := checkLog_sound (w := (85 / 2027)) (n := 12)
    (lo := (16783399 / 200000000)) (hi := (20979249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 971) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 971) = 1/(971 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_82 : (130602449 / 500000000) ≤ -Real.log (3253 / 4224) ∧
    -Real.log (3253 / 4224) ≤ (261204899 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 7477)) (n := 12)
    (lo := (130602449 / 500000000)) (hi := (261204899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3253) = 1/(3253 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_83 : (730237589 / 500000000) ≤ -Real.log (1961 / 8448) ∧
    -Real.log (1961 / 8448) ≤ (1460475181 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 4073)) (n := 12)
    (lo := (37090409 / 500000000)) (hi := (74180819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1961) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1961) = 1/(1961 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_83 : (16508097 / 62500000) ≤ -Real.log (6487 / 8448) ∧
    -Real.log (6487 / 8448) ≤ (264129553 / 1000000000) := by
  have h := checkLog_sound (w := (1961 / 14935)) (n := 12)
    (lo := (16508097 / 62500000)) (hi := (264129553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6487) = 1/(6487 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_84 : (1450832881 / 1000000000) ≤ -Real.log (15 / 64) ∧
    -Real.log (15 / 64) ≤ (362708221 / 250000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 15) = 1/(15 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_84 : (53412557 / 200000000) ≤ -Real.log (49 / 64) ∧
    -Real.log (49 / 64) ≤ (133531393 / 500000000) := by
  have h := checkLog_sound (w := (15 / 113)) (n := 12)
    (lo := (53412557 / 200000000)) (hi := (133531393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 49) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 49) = 1/(49 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_85 : (144128267 / 100000000) ≤ -Real.log (1999 / 8448) ∧
    -Real.log (1999 / 8448) ≤ (1441282673 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 4111)) (n := 12)
    (lo := (5498831 / 100000000)) (hi := (54988311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1999) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1999) = 1/(1999 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_85 : (135002323 / 500000000) ≤ -Real.log (6449 / 8448) ∧
    -Real.log (6449 / 8448) ≤ (270004647 / 1000000000) := by
  have h := checkLog_sound (w := (1999 / 14897)) (n := 12)
    (lo := (135002323 / 500000000)) (hi := (270004647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6449) = 1/(6449 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_86 : (1431822803 / 1000000000) ≤ -Real.log (1009 / 4224) ∧
    -Real.log (1009 / 4224) ≤ (715911403 / 500000000) := by
  have h := checkLog_sound (w := (47 / 2065)) (n := 12)
    (lo := (45528443 / 1000000000)) (hi := (11382111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 1009) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 1009) = 1/(1009 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_86 : (68238797 / 250000000) ≤ -Real.log (3215 / 4224) ∧
    -Real.log (3215 / 4224) ≤ (272955189 / 1000000000) := by
  have h := checkLog_sound (w := (1009 / 7439)) (n := 12)
    (lo := (68238797 / 250000000)) (hi := (272955189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3215) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3215) = 1/(3215 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_87 : (355612897 / 250000000) ≤ -Real.log (679 / 2816) ∧
    -Real.log (679 / 2816) ≤ (1422451591 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 1383)) (n := 12)
    (lo := (9039307 / 250000000)) (hi := (36157229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 679) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 679) = 1/(679 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_87 : (275914461 / 1000000000) ≤ -Real.log (2137 / 2816) ∧
    -Real.log (2137 / 2816) ≤ (137957231 / 500000000) := by
  have h := checkLog_sound (w := (679 / 4953)) (n := 12)
    (lo := (275914461 / 1000000000)) (hi := (137957231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2137) = 1/(2137 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_88 : (706583689 / 500000000) ≤ -Real.log (257 / 1056) ∧
    -Real.log (257 / 1056) ≤ (1413167381 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 521)) (n := 12)
    (lo := (13436509 / 500000000)) (hi := (26873019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264 / 257) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(264 / 257) = 1/(257 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_88 : (139441259 / 500000000) ≤ -Real.log (799 / 1056) ∧
    -Real.log (799 / 1056) ≤ (278882519 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 1855)) (n := 12)
    (lo := (139441259 / 500000000)) (hi := (278882519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1056 / 799) = 1/(799 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_89 : (350992143 / 250000000) ≤ -Real.log (2075 / 8448) ∧
    -Real.log (2075 / 8448) ≤ (56158743 / 40000000) := by
  have h := checkLog_sound (w := (37 / 4187)) (n := 12)
    (lo := (4418553 / 250000000)) (hi := (17674213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 2075) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 2075) = 1/(2075 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_89 : (28185941 / 100000000) ≤ -Real.log (6373 / 8448) ∧
    -Real.log (6373 / 8448) ≤ (281859411 / 1000000000) := by
  have h := checkLog_sound (w := (2075 / 14821)) (n := 12)
    (lo := (28185941 / 100000000)) (hi := (281859411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6373) = 1/(6373 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_90 : (1394853613 / 1000000000) ≤ -Real.log (349 / 1408) ∧
    -Real.log (349 / 1408) ≤ (87178351 / 62500000) := by
  have h := checkLog_sound (w := (3 / 701)) (n := 12)
    (lo := (8559253 / 1000000000)) (hi := (4279627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 349) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(352 / 349) = 1/(349 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_90 : (284845191 / 1000000000) ≤ -Real.log (1059 / 1408) ∧
    -Real.log (1059 / 1408) ≤ (35605649 / 125000000) := by
  have h := checkLog_sound (w := (349 / 2467)) (n := 12)
    (lo := (284845191 / 1000000000)) (hi := (35605649 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1059) = 1/(1059 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_91 : (68843461 / 50000000) ≤ -Real.log (533 / 2112) ∧
    -Real.log (533 / 2112) ≤ (688434611 / 500000000) := by
  have h := checkLog_sound (w := (523 / 1589)) (n := 12)
    (lo := (17093051 / 25000000)) (hi := (683722041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 533) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056 / 533) = 1/(533 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_91 : (29084363 / 100000000) ≤ -Real.log (1579 / 2112) ∧
    -Real.log (1579 / 2112) ≤ (290843631 / 1000000000) := by
  have h := checkLog_sound (w := (533 / 3691)) (n := 12)
    (lo := (29084363 / 100000000)) (hi := (290843631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1579) = 1/(1579 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_92 : (679601279 / 500000000) ≤ -Real.log (1085 / 4224) ∧
    -Real.log (1085 / 4224) ≤ (1061877 / 781250) := by
  have h := checkLog_sound (w := (1027 / 3197)) (n := 12)
    (lo := (333027689 / 500000000)) (hi := (666055379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1085) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2112 / 1085) = 1/(1085 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_92 : (74219567 / 250000000) ≤ -Real.log (3139 / 4224) ∧
    -Real.log (3139 / 4224) ≤ (296878269 / 1000000000) := by
  have h := checkLog_sound (w := (1085 / 7363)) (n := 12)
    (lo := (74219567 / 250000000)) (hi := (296878269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3139) = 1/(3139 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_93 : (1341842597 / 1000000000) ≤ -Real.log (23 / 88) ∧
    -Real.log (23 / 88) ≤ (1341842599 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 67)) (n := 12)
    (lo := (648695417 / 1000000000)) (hi := (324347709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44 / 23) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(44 / 23) = 1/(23 / 88) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_93 : (37868693 / 125000000) ≤ -Real.log (65 / 88) ∧
    -Real.log (65 / 88) ≤ (60589909 / 200000000) := by
  have h := checkLog_sound (w := (23 / 153)) (n := 12)
    (lo := (37868693 / 125000000)) (hi := (60589909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88 / 65) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88 / 65) = 1/(65 / 88) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_94 : (132477887 / 100000000) ≤ -Real.log (1123 / 4224) ∧
    -Real.log (1123 / 4224) ≤ (165597359 / 125000000) := by
  have h := checkLog_sound (w := (989 / 3235)) (n := 12)
    (lo := (63163169 / 100000000)) (hi := (631631691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2112 / 1123) = 1/(1123 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_94 : (154528953 / 500000000) ≤ -Real.log (3101 / 4224) ∧
    -Real.log (3101 / 4224) ≤ (309057907 / 1000000000) := by
  have h := checkLog_sound (w := (1123 / 7325)) (n := 12)
    (lo := (154528953 / 500000000)) (hi := (309057907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3101) = 1/(3101 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_95 : (654000717 / 500000000) ≤ -Real.log (571 / 2112) ∧
    -Real.log (571 / 2112) ≤ (327000359 / 250000000) := by
  have h := checkLog_sound (w := (485 / 1627)) (n := 12)
    (lo := (307427127 / 500000000)) (hi := (122970851 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 571) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056 / 571) = 1/(571 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_95 : (315203809 / 1000000000) ≤ -Real.log (1541 / 2112) ∧
    -Real.log (1541 / 2112) ≤ (31520381 / 100000000) := by
  have h := checkLog_sound (w := (571 / 3653)) (n := 12)
    (lo := (315203809 / 1000000000)) (hi := (31520381 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1541) = 1/(1541 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

end GeneralCK.Certificates.Mixed


