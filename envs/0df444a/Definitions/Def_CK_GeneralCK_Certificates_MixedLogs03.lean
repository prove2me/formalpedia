-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLogs03
-- name    : CK_GeneralCK_Certificates_MixedLogs03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:24:56.138418+00:00
-- url     : https://prove2.me/theorems/950b5bae-cc03-4406-91f8-82d53aa1044a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLogs03` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLogs03` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLogs03` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLogs03 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLogs03.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_v_48 : (1874647127 / 1000000000) ≤ -Real.log (27 / 176) ∧
    -Real.log (27 / 176) ≤ (187464713 / 100000000) := by
  have h := checkLog_sound (w := (17 / 71)) (n := 12)
    (lo := (488352767 / 1000000000)) (hi := (953814 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(44 / 27) = 1/(27 / 176) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_48 : (166537689 / 1000000000) ≤ -Real.log (149 / 176) ∧
    -Real.log (149 / 176) ≤ (16653769 / 100000000) := by
  have h := checkLog_sound (w := (27 / 325)) (n := 12)
    (lo := (166537689 / 1000000000)) (hi := (16653769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176 / 149) = 1/(149 / 176) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_49 : (93004653 / 50000000) ≤ -Real.log (1315 / 8448) ∧
    -Real.log (1315 / 8448) ≤ (1860093063 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 3427)) (n := 12)
    (lo := (4737987 / 10000000)) (hi := (473798701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1315) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1315) = 1/(1315 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_49 : (169197823 / 1000000000) ≤ -Real.log (7133 / 8448) ∧
    -Real.log (7133 / 8448) ≤ (660929 / 3906250) := by
  have h := checkLog_sound (w := (1315 / 15581)) (n := 12)
    (lo := (169197823 / 1000000000)) (hi := (660929 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7133) = 1/(7133 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_50 : (922873889 / 500000000) ≤ -Real.log (667 / 4224) ∧
    -Real.log (667 / 4224) ≤ (1845747781 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 1723)) (n := 12)
    (lo := (229726709 / 500000000)) (hi := (459453419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 667) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 667) = 1/(667 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_50 : (171865053 / 1000000000) ≤ -Real.log (3557 / 4224) ∧
    -Real.log (3557 / 4224) ≤ (85932527 / 500000000) := by
  have h := checkLog_sound (w := (667 / 7781)) (n := 12)
    (lo := (171865053 / 1000000000)) (hi := (85932527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3557) = 1/(3557 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_51 : (14309417 / 7812500) ≤ -Real.log (41 / 256) ∧
    -Real.log (41 / 256) ≤ (1831605379 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 41) = 1/(41 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_51 : (21817427 / 125000000) ≤ -Real.log (215 / 256) ∧
    -Real.log (215 / 256) ≤ (174539417 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 471)) (n := 12)
    (lo := (21817427 / 125000000)) (hi := (174539417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 215) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 215) = 1/(215 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_52 : (454415049 / 250000000) ≤ -Real.log (343 / 2112) ∧
    -Real.log (343 / 2112) ≤ (1817660199 / 1000000000) := by
  have h := checkLog_sound (w := (185 / 871)) (n := 12)
    (lo := (107841459 / 250000000)) (hi := (431365837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 343) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(528 / 343) = 1/(343 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_52 : (3544419 / 20000000) ≤ -Real.log (1769 / 2112) ∧
    -Real.log (1769 / 2112) ≤ (177220951 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 3881)) (n := 12)
    (lo := (3544419 / 20000000)) (hi := (177220951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1769) = 1/(1769 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_53 : (450976703 / 250000000) ≤ -Real.log (1391 / 8448) ∧
    -Real.log (1391 / 8448) ≤ (360781363 / 200000000) := by
  have h := checkLog_sound (w := (721 / 3503)) (n := 12)
    (lo := (104403113 / 250000000)) (hi := (417612453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1391) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1391) = 1/(1391 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_53 : (89954847 / 500000000) ≤ -Real.log (7057 / 8448) ∧
    -Real.log (7057 / 8448) ≤ (35981939 / 200000000) := by
  have h := checkLog_sound (w := (1391 / 15505)) (n := 12)
    (lo := (89954847 / 500000000)) (hi := (35981939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7057) = 1/(7057 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_54 : (1790340021 / 1000000000) ≤ -Real.log (235 / 1408) ∧
    -Real.log (235 / 1408) ≤ (223792503 / 125000000) := by
  have h := checkLog_sound (w := (117 / 587)) (n := 12)
    (lo := (404045661 / 1000000000)) (hi := (202022831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 235) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(352 / 235) = 1/(235 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_54 : (22825711 / 125000000) ≤ -Real.log (1173 / 1408) ∧
    -Real.log (1173 / 1408) ≤ (182605689 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 2581)) (n := 12)
    (lo := (22825711 / 125000000)) (hi := (182605689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1173) = 1/(1173 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_55 : (888477413 / 500000000) ≤ -Real.log (1429 / 8448) ∧
    -Real.log (1429 / 8448) ≤ (1776954829 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 3541)) (n := 12)
    (lo := (195330233 / 500000000)) (hi := (390660467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1429) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1429) = 1/(1429 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_55 : (185308969 / 1000000000) ≤ -Real.log (7019 / 8448) ∧
    -Real.log (7019 / 8448) ≤ (18530897 / 100000000) := by
  have h := checkLog_sound (w := (1429 / 15467)) (n := 12)
    (lo := (185308969 / 1000000000)) (hi := (18530897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 7019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 7019) = 1/(7019 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_56 : (1763746431 / 1000000000) ≤ -Real.log (181 / 1056) ∧
    -Real.log (181 / 1056) ≤ (881873217 / 500000000) := by
  have h := checkLog_sound (w := (83 / 445)) (n := 12)
    (lo := (377452071 / 1000000000)) (hi := (47181509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264 / 181) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(264 / 181) = 1/(181 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_56 : (188019577 / 1000000000) ≤ -Real.log (875 / 1056) ∧
    -Real.log (875 / 1056) ≤ (94009789 / 500000000) := by
  have h := checkLog_sound (w := (181 / 1931)) (n := 12)
    (lo := (188019577 / 1000000000)) (hi := (94009789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 875) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1056 / 875) = 1/(875 / 1056) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_57 : (875355113 / 500000000) ≤ -Real.log (489 / 2816) ∧
    -Real.log (489 / 2816) ≤ (1750710229 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 1193)) (n := 12)
    (lo := (182207933 / 500000000)) (hi := (364415867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 489) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 489) = 1/(489 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_57 : (190737553 / 1000000000) ≤ -Real.log (2327 / 2816) ∧
    -Real.log (2327 / 2816) ≤ (95368777 / 500000000) := by
  have h := checkLog_sound (w := (489 / 5143)) (n := 12)
    (lo := (190737553 / 1000000000)) (hi := (95368777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2327) = 1/(2327 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_58 : (1737841779 / 1000000000) ≤ -Real.log (743 / 4224) ∧
    -Real.log (743 / 4224) ≤ (868920891 / 500000000) := by
  have h := checkLog_sound (w := (313 / 1799)) (n := 12)
    (lo := (351547419 / 1000000000)) (hi := (17577371 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 743) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 743) = 1/(743 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_58 : (193462937 / 1000000000) ≤ -Real.log (3481 / 4224) ∧
    -Real.log (3481 / 4224) ≤ (96731469 / 500000000) := by
  have h := checkLog_sound (w := (743 / 7705)) (n := 12)
    (lo := (193462937 / 1000000000)) (hi := (96731469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3481) = 1/(3481 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_59 : (1725136827 / 1000000000) ≤ -Real.log (1505 / 8448) ∧
    -Real.log (1505 / 8448) ≤ (172513683 / 100000000) := by
  have h := checkLog_sound (w := (607 / 3617)) (n := 12)
    (lo := (338842467 / 1000000000)) (hi := (84710617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1505) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1505) = 1/(1505 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_59 : (196195769 / 1000000000) ≤ -Real.log (6943 / 8448) ∧
    -Real.log (6943 / 8448) ≤ (19619577 / 100000000) := by
  have h := checkLog_sound (w := (1505 / 15391)) (n := 12)
    (lo := (196195769 / 1000000000)) (hi := (19619577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6943) = 1/(6943 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_60 : (428147817 / 250000000) ≤ -Real.log (127 / 704) ∧
    -Real.log (127 / 704) ≤ (1712591271 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 303)) (n := 12)
    (lo := (81574227 / 250000000)) (hi := (326296909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 127) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(176 / 127) = 1/(127 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_60 : (198936089 / 1000000000) ≤ -Real.log (577 / 704) ∧
    -Real.log (577 / 704) ≤ (19893609 / 100000000) := by
  have h := checkLog_sound (w := (127 / 1281)) (n := 12)
    (lo := (198936089 / 1000000000)) (hi := (19893609 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704 / 577) = 1/(577 / 704) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_61 : (26565643 / 15625000) ≤ -Real.log (1543 / 8448) ∧
    -Real.log (1543 / 8448) ≤ (340040231 / 200000000) := by
  have h := checkLog_sound (w := (569 / 3655)) (n := 12)
    (lo := (39238349 / 125000000)) (hi := (313906793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1543) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1543) = 1/(1543 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_61 : (10084197 / 50000000) ≤ -Real.log (6905 / 8448) ∧
    -Real.log (6905 / 8448) ≤ (201683941 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 15353)) (n := 12)
    (lo := (10084197 / 50000000)) (hi := (201683941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6905) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6905) = 1/(6905 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_62 : (843981337 / 500000000) ≤ -Real.log (71 / 384) ∧
    -Real.log (71 / 384) ≤ (1687962677 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 167)) (n := 12)
    (lo := (150834157 / 500000000)) (hi := (60333663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 71) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(96 / 71) = 1/(71 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_62 : (102219681 / 500000000) ≤ -Real.log (313 / 384) ∧
    -Real.log (313 / 384) ≤ (204439363 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 697)) (n := 12)
    (lo := (102219681 / 500000000)) (hi := (204439363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384 / 313) = 1/(313 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_63 : (1675872167 / 1000000000) ≤ -Real.log (527 / 2816) ∧
    -Real.log (527 / 2816) ≤ (167587217 / 100000000) := by
  have h := checkLog_sound (w := (177 / 1231)) (n := 12)
    (lo := (289577807 / 1000000000)) (hi := (18098613 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 527) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 527) = 1/(527 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_63 : (207202397 / 1000000000) ≤ -Real.log (2289 / 2816) ∧
    -Real.log (2289 / 2816) ≤ (103601199 / 500000000) := by
  have h := checkLog_sound (w := (527 / 5105)) (n := 12)
    (lo := (207202397 / 1000000000)) (hi := (103601199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2289) = 1/(2289 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

end GeneralCK.Certificates.Mixed


