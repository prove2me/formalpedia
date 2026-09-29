-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLogs04
-- name    : CK_GeneralCK_Certificates_MixedLogs04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:23:09.061906+00:00
-- url     : https://prove2.me/theorems/42a01037-b761-440a-a0cd-279dbc1f0955
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLogs04` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLogs04` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLogs04` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLogs04 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLogs04.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_v_64 : (103995381 / 62500000) ≤ -Real.log (25 / 132) ∧
    -Real.log (25 / 132) ≤ (1663926099 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 29)) (n := 12)
    (lo := (34703967 / 125000000)) (hi := (277631737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33 / 25) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(33 / 25) = 1/(25 / 132) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_64 : (6561659 / 31250000) ≤ -Real.log (107 / 132) ∧
    -Real.log (107 / 132) ≤ (209973089 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 239)) (n := 12)
    (lo := (6561659 / 31250000)) (hi := (209973089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132 / 107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132 / 107) = 1/(107 / 132) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_65 : (1652121051 / 1000000000) ≤ -Real.log (1619 / 8448) ∧
    -Real.log (1619 / 8448) ≤ (826060527 / 500000000) := by
  have h := checkLog_sound (w := (493 / 3731)) (n := 12)
    (lo := (265826691 / 1000000000)) (hi := (66456673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1619) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1619) = 1/(1619 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_65 : (53187869 / 250000000) ≤ -Real.log (6829 / 8448) ∧
    -Real.log (6829 / 8448) ≤ (212751477 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 15277)) (n := 12)
    (lo := (53187869 / 250000000)) (hi := (212751477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6829) = 1/(6829 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_66 : (82022687 / 50000000) ≤ -Real.log (273 / 1408) ∧
    -Real.log (273 / 1408) ≤ (1640453743 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 625)) (n := 12)
    (lo := (12707969 / 50000000)) (hi := (254159381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(352 / 273) = 1/(273 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_66 : (107768803 / 500000000) ≤ -Real.log (1135 / 1408) ∧
    -Real.log (1135 / 1408) ≤ (215537607 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 2543)) (n := 12)
    (lo := (107768803 / 500000000)) (hi := (215537607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1135) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1135) = 1/(1135 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_67 : (1628920987 / 1000000000) ≤ -Real.log (1657 / 8448) ∧
    -Real.log (1657 / 8448) ≤ (162892099 / 100000000) := by
  have h := checkLog_sound (w := (455 / 3769)) (n := 12)
    (lo := (242626627 / 1000000000)) (hi := (60656657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1657) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1657) = 1/(1657 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_67 : (341143 / 1562500) ≤ -Real.log (6791 / 8448) ∧
    -Real.log (6791 / 8448) ≤ (218331521 / 1000000000) := by
  have h := checkLog_sound (w := (1657 / 15239)) (n := 12)
    (lo := (341143 / 1562500)) (hi := (218331521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6791) = 1/(6791 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_68 : (1617519723 / 1000000000) ≤ -Real.log (419 / 2112) ∧
    -Real.log (419 / 2112) ≤ (808759863 / 500000000) := by
  have h := checkLog_sound (w := (109 / 947)) (n := 12)
    (lo := (231225363 / 1000000000)) (hi := (57806341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 419) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(528 / 419) = 1/(419 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_68 : (110566631 / 500000000) ≤ -Real.log (1693 / 2112) ∧
    -Real.log (1693 / 2112) ≤ (221133263 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 3805)) (n := 12)
    (lo := (110566631 / 500000000)) (hi := (221133263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1693) = 1/(1693 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_69 : (321249397 / 200000000) ≤ -Real.log (565 / 2816) ∧
    -Real.log (565 / 2816) ≤ (401561747 / 250000000) := by
  have h := checkLog_sound (w := (139 / 1269)) (n := 12)
    (lo := (1759621 / 8000000)) (hi := (109976313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 565) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 565) = 1/(565 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_69 : (55985719 / 250000000) ≤ -Real.log (2251 / 2816) ∧
    -Real.log (2251 / 2816) ≤ (223942877 / 1000000000) := by
  have h := checkLog_sound (w := (565 / 5067)) (n := 12)
    (lo := (55985719 / 250000000)) (hi := (223942877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2251) = 1/(2251 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_70 : (319019981 / 200000000) ≤ -Real.log (857 / 4224) ∧
    -Real.log (857 / 4224) ≤ (398774977 / 250000000) := by
  have h := checkLog_sound (w := (199 / 1913)) (n := 12)
    (lo := (41761109 / 200000000)) (hi := (104402773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 857) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 857) = 1/(857 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_70 : (113380203 / 500000000) ≤ -Real.log (3367 / 4224) ∧
    -Real.log (3367 / 4224) ≤ (226760407 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 7591)) (n := 12)
    (lo := (113380203 / 500000000)) (hi := (226760407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3367) = 1/(3367 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_71 : (316815143 / 200000000) ≤ -Real.log (1733 / 8448) ∧
    -Real.log (1733 / 8448) ≤ (792037859 / 500000000) := by
  have h := checkLog_sound (w := (379 / 3845)) (n := 12)
    (lo := (39556271 / 200000000)) (hi := (49445339 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1733) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1733) = 1/(1733 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_71 : (28698237 / 125000000) ≤ -Real.log (6715 / 8448) ∧
    -Real.log (6715 / 8448) ≤ (229585897 / 1000000000) := by
  have h := checkLog_sound (w := (1733 / 15163)) (n := 12)
    (lo := (28698237 / 125000000)) (hi := (229585897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6715) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6715) = 1/(6715 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_72 : (1573171733 / 1000000000) ≤ -Real.log (73 / 352) ∧
    -Real.log (73 / 352) ≤ (196646467 / 125000000) := by
  have h := checkLog_sound (w := (15 / 161)) (n := 12)
    (lo := (186877373 / 1000000000)) (hi := (93438687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88 / 73) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(88 / 73) = 1/(73 / 352) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_72 : (232419393 / 1000000000) ≤ -Real.log (279 / 352) ∧
    -Real.log (279 / 352) ≤ (116209697 / 500000000) := by
  have h := checkLog_sound (w := (73 / 631)) (n := 12)
    (lo := (232419393 / 1000000000)) (hi := (116209697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352 / 279) = 1/(279 / 352) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_73 : (1562385367 / 1000000000) ≤ -Real.log (161 / 768) ∧
    -Real.log (161 / 768) ≤ (156238537 / 100000000) := by
  have h := checkLog_sound (w := (31 / 353)) (n := 12)
    (lo := (176091007 / 1000000000)) (hi := (1375711 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 161) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(192 / 161) = 1/(161 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_73 : (117630471 / 500000000) ≤ -Real.log (607 / 768) ∧
    -Real.log (607 / 768) ≤ (235260943 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1375)) (n := 12)
    (lo := (117630471 / 500000000)) (hi := (235260943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768 / 607) = 1/(607 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_74 : (310342821 / 200000000) ≤ -Real.log (895 / 4224) ∧
    -Real.log (895 / 4224) ≤ (387928527 / 250000000) := by
  have h := checkLog_sound (w := (161 / 1951)) (n := 12)
    (lo := (33083949 / 200000000)) (hi := (82709873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056 / 895) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1056 / 895) = 1/(895 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_74 : (238110587 / 1000000000) ≤ -Real.log (3329 / 4224) ∧
    -Real.log (3329 / 4224) ≤ (59527647 / 250000000) := by
  have h := checkLog_sound (w := (895 / 7553)) (n := 12)
    (lo := (238110587 / 1000000000)) (hi := (59527647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4224 / 3329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4224 / 3329) = 1/(3329 / 4224) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_75 : (1541155519 / 1000000000) ≤ -Real.log (603 / 2816) ∧
    -Real.log (603 / 2816) ≤ (770577761 / 500000000) := by
  have h := checkLog_sound (w := (101 / 1307)) (n := 12)
    (lo := (154861159 / 1000000000)) (hi := (3871529 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704 / 603) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(704 / 603) = 1/(603 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_75 : (240968377 / 1000000000) ≤ -Real.log (2213 / 2816) ∧
    -Real.log (2213 / 2816) ≤ (120484189 / 500000000) := by
  have h := checkLog_sound (w := (603 / 5029)) (n := 12)
    (lo := (240968377 / 1000000000)) (hi := (120484189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2816 / 2213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2816 / 2213) = 1/(2213 / 2816) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_76 : (382676813 / 250000000) ≤ -Real.log (457 / 2112) ∧
    -Real.log (457 / 2112) ≤ (306141451 / 200000000) := by
  have h := checkLog_sound (w := (71 / 985)) (n := 12)
    (lo := (36103223 / 250000000)) (hi := (144412893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528 / 457) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(528 / 457) = 1/(457 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_76 : (243834357 / 1000000000) ≤ -Real.log (1655 / 2112) ∧
    -Real.log (1655 / 2112) ≤ (121917179 / 500000000) := by
  have h := checkLog_sound (w := (457 / 3767)) (n := 12)
    (lo := (243834357 / 1000000000)) (hi := (121917179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1655) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112 / 1655) = 1/(1655 / 2112) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_77 : (95022939 / 62500000) ≤ -Real.log (1847 / 8448) ∧
    -Real.log (1847 / 8448) ≤ (1520367027 / 1000000000) := by
  have h := checkLog_sound (w := (265 / 3959)) (n := 12)
    (lo := (16759083 / 125000000)) (hi := (26814533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1847) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1847) = 1/(1847 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_77 : (123354287 / 500000000) ≤ -Real.log (6601 / 8448) ∧
    -Real.log (6601 / 8448) ≤ (9868343 / 40000000) := by
  have h := checkLog_sound (w := (1847 / 15049)) (n := 12)
    (lo := (123354287 / 500000000)) (hi := (9868343 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6601) = 1/(6601 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_78 : (1510132623 / 1000000000) ≤ -Real.log (311 / 1408) ∧
    -Real.log (311 / 1408) ≤ (755066313 / 500000000) := by
  have h := checkLog_sound (w := (41 / 663)) (n := 12)
    (lo := (123838263 / 1000000000)) (hi := (15479783 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352 / 311) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(352 / 311) = 1/(311 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_78 : (62397769 / 250000000) ≤ -Real.log (1097 / 1408) ∧
    -Real.log (1097 / 1408) ≤ (249591077 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 2505)) (n := 12)
    (lo := (62397769 / 250000000)) (hi := (249591077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408 / 1097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408 / 1097) = 1/(1097 / 1408) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_v_79 : (93750119 / 62500000) ≤ -Real.log (1885 / 8448) ∧
    -Real.log (1885 / 8448) ≤ (1500001907 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 3997)) (n := 12)
    (lo := (14213443 / 125000000)) (hi := (22741509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112 / 1885) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2112 / 1885) = 1/(1885 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_79 : (252481911 / 1000000000) ≤ -Real.log (6563 / 8448) ∧
    -Real.log (6563 / 8448) ≤ (31560239 / 125000000) := by
  have h := checkLog_sound (w := (1885 / 15011)) (n := 12)
    (lo := (252481911 / 1000000000)) (hi := (31560239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8448 / 6563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8448 / 6563) = 1/(6563 / 8448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

end GeneralCK.Certificates.Mixed


