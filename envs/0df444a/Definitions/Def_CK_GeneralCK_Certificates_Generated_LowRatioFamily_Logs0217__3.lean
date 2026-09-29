-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:55:49.466961+00:00
-- url     : https://prove2.me/theorems/bef162f4-d93f-46b6-9318-e8c077347022
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0217 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0218, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0219).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14016_neg : (253574587 / 250000000) ≤ -Real.log (31250000000 / 86169623919) ∧
    -Real.log (31250000000 / 86169623919) ≤ (20285967 / 20000000) := by
  have h := checkLog_sound (w := (23669623919 / 148669623919)) (n := 12)
    (lo := (5017987 / 15625000)) (hi := (321151169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86169623919 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(86169623919 / 62500000000) = 1/(31250000000 / 86169623919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14016 : Bounds (253574587 / 250000000) (20285967 / 20000000) (Real.log (86169623919 / 31250000000)) := by
  have h := reflection_log_14016_neg
  have he : Real.log (86169623919 / 31250000000) = -Real.log (31250000000 / 86169623919) := by
    rw [show ((86169623919 / 31250000000) : ℝ) = ((31250000000 / 86169623919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14017_neg : (511021859 / 500000000) ≤ -Real.log (100000000000 / 277886819119) ∧
    -Real.log (100000000000 / 277886819119) ≤ (25551093 / 25000000) := by
  have h := checkLog_sound (w := (77886819119 / 477886819119)) (n := 12)
    (lo := (164448269 / 500000000)) (hi := (328896539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277886819119 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(277886819119 / 200000000000) = 1/(100000000000 / 277886819119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14017 : Bounds (511021859 / 500000000) (25551093 / 25000000) (Real.log (277886819119 / 100000000000)) := by
  have h := reflection_log_14017_neg
  have he : Real.log (277886819119 / 100000000000) = -Real.log (100000000000 / 277886819119) := by
    rw [show ((277886819119 / 100000000000) : ℝ) = ((100000000000 / 277886819119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14018_neg : (1132872261 / 500000000) ≤ -Real.log (50000000000 / 481914893617) ∧
    -Real.log (50000000000 / 481914893617) ≤ (1132872263 / 500000000) := by
  have h := checkLog_sound (w := (81914893617 / 881914893617)) (n := 12)
    (lo := (93151491 / 500000000)) (hi := (186302983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481914893617 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(481914893617 / 400000000000) = 1/(50000000000 / 481914893617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14018 : Bounds (1132872261 / 500000000) (1132872263 / 500000000) (Real.log (481914893617 / 50000000000)) := by
  have h := reflection_log_14018_neg
  have he : Real.log (481914893617 / 50000000000) = -Real.log (50000000000 / 481914893617) := by
    rw [show ((481914893617 / 50000000000) : ℝ) = ((50000000000 / 481914893617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14019_neg : (2283484919 / 1000000000) ≤ -Real.log (250000000000 / 2452702702703) ∧
    -Real.log (250000000000 / 2452702702703) ≤ (2283484923 / 1000000000) := by
  have h := checkLog_sound (w := (452702702703 / 4452702702703)) (n := 12)
    (lo := (204043379 / 1000000000)) (hi := (10202169 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2452702702703 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2452702702703 / 2000000000000) = 1/(250000000000 / 2452702702703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14019 : Bounds (2283484919 / 1000000000) (2283484923 / 1000000000) (Real.log (2452702702703 / 250000000000)) := by
  have h := reflection_log_14019_neg
  have he : Real.log (2452702702703 / 250000000000) = -Real.log (250000000000 / 2452702702703) := by
    rw [show ((2452702702703 / 250000000000) : ℝ) = ((250000000000 / 2452702702703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14020_neg : (119547399 / 200000000) ≤ -Real.log (500 / 909) ∧
    -Real.log (500 / 909) ≤ (149434249 / 250000000) := by
  have h := checkLog_sound (w := (409 / 1409)) (n := 12)
    (lo := (119547399 / 200000000)) (hi := (149434249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909 / 500) = 1/(500 / 909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14020 : Bounds (119547399 / 200000000) (149434249 / 250000000) (Real.log (909 / 500)) := by
  have h := reflection_log_14020_neg
  have he : Real.log (909 / 500) = -Real.log (500 / 909) := by
    rw [show ((909 / 500) : ℝ) = ((500 / 909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14021_neg : (170374859 / 100000000) ≤ -Real.log (91 / 500) ∧
    -Real.log (91 / 500) ≤ (1703748593 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 108)) (n := 12)
    (lo := (31745423 / 100000000)) (hi := (317454231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 91) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 91) = 1/(91 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14021 : Bounds (-1703748593 / 1000000000) (-170374859 / 100000000) (Real.log (91 / 500)) := by
  have h := reflection_log_14021_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14022_neg : (163533 / 200000000) ≤ -Real.log (500000 / 500409) ∧
    -Real.log (500000 / 500409) ≤ (408833 / 500000000) := by
  have h := checkLog_sound (w := (409 / 1000409)) (n := 12)
    (lo := (163533 / 200000000)) (hi := (408833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500409 / 500000) = 1/(500000 / 500409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14022 : Bounds (163533 / 200000000) (408833 / 500000000) (Real.log (500409 / 500000)) := by
  have h := reflection_log_14022_neg
  have he : Real.log (500409 / 500000) = -Real.log (500000 / 500409) := by
    rw [show ((500409 / 500000) : ℝ) = ((500000 / 500409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14023_neg : (409167 / 500000000) ≤ -Real.log (499591 / 500000) ∧
    -Real.log (499591 / 500000) ≤ (163667 / 200000000) := by
  have h := checkLog_sound (w := (409 / 999591)) (n := 12)
    (lo := (409167 / 500000000)) (hi := (163667 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499591) = 1/(499591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14023 : Bounds (-163667 / 200000000) (-409167 / 500000000) (Real.log (499591 / 500000)) := by
  have h := reflection_log_14023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14024_neg : (385313419 / 1000000000) ≤ -Real.log (40000 / 58803) ∧
    -Real.log (40000 / 58803) ≤ (19265671 / 50000000) := by
  have h := checkLog_sound (w := (18803 / 98803)) (n := 12)
    (lo := (385313419 / 1000000000)) (hi := (19265671 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58803 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58803 / 40000) = 1/(40000 / 58803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14024 : Bounds (385313419 / 1000000000) (19265671 / 50000000) (Real.log (58803 / 40000)) := by
  have h := reflection_log_14024_neg
  have he : Real.log (58803 / 40000) = -Real.log (40000 / 58803) := by
    rw [show ((58803 / 40000) : ℝ) = ((40000 / 58803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14025_neg : (635019791 / 1000000000) ≤ -Real.log (21197 / 40000) ∧
    -Real.log (21197 / 40000) ≤ (39688737 / 62500000) := by
  have h := checkLog_sound (w := (18803 / 61197)) (n := 12)
    (lo := (635019791 / 1000000000)) (hi := (39688737 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 21197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 21197) = 1/(21197 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14025 : Bounds (-39688737 / 62500000) (-635019791 / 1000000000) (Real.log (21197 / 40000)) := by
  have h := reflection_log_14025_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14026_neg : (15494951 / 40000000) ≤ -Real.log (1000000 / 1473107) ∧
    -Real.log (1000000 / 1473107) ≤ (24210861 / 62500000) := by
  have h := checkLog_sound (w := (473107 / 2473107)) (n := 12)
    (lo := (15494951 / 40000000)) (hi := (24210861 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473107 / 1000000) = 1/(1000000 / 1473107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14026 : Bounds (15494951 / 40000000) (24210861 / 62500000) (Real.log (1473107 / 1000000)) := by
  have h := reflection_log_14026_neg
  have he : Real.log (1473107 / 1000000) = -Real.log (1000000 / 1473107) := by
    rw [show ((1473107 / 1000000) : ℝ) = ((1000000 / 1473107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14027_neg : (640757787 / 1000000000) ≤ -Real.log (526893 / 1000000) ∧
    -Real.log (526893 / 1000000) ≤ (160189447 / 250000000) := by
  have h := checkLog_sound (w := (473107 / 1526893)) (n := 12)
    (lo := (640757787 / 1000000000)) (hi := (160189447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 526893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 526893) = 1/(526893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14027 : Bounds (-160189447 / 250000000) (-640757787 / 1000000000) (Real.log (526893 / 1000000)) := by
  have h := reflection_log_14027_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14028_neg : (253384011 / 1000000000) ≤ -Real.log (776169766551 / 1000000000000) ∧
    -Real.log (776169766551 / 1000000000000) ≤ (63346003 / 250000000) := by
  have h := checkLog_sound (w := (223830233449 / 1776169766551)) (n := 12)
    (lo := (253384011 / 1000000000)) (hi := (63346003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 776169766551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 776169766551) = 1/(776169766551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14028 : Bounds (-63346003 / 250000000) (-253384011 / 1000000000) (Real.log (776169766551 / 1000000000000)) := by
  have h := reflection_log_14028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14029_neg : (249706371 / 1000000000) ≤ -Real.log (1246447191 / 1600000000) ∧
    -Real.log (1246447191 / 1600000000) ≤ (62426593 / 250000000) := by
  have h := checkLog_sound (w := (353552809 / 2846447191)) (n := 12)
    (lo := (249706371 / 1000000000)) (hi := (62426593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1246447191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1246447191) = 1/(1246447191 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14029 : Bounds (-62426593 / 250000000) (-249706371 / 1000000000) (Real.log (1246447191 / 1600000000)) := by
  have h := reflection_log_14029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14030_neg : (1020333211 / 1000000000) ≤ -Real.log (10000000000 / 27741189791) ∧
    -Real.log (10000000000 / 27741189791) ≤ (1020333213 / 1000000000) := by
  have h := checkLog_sound (w := (7741189791 / 47741189791)) (n := 12)
    (lo := (327186031 / 1000000000)) (hi := (20449127 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27741189791 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(27741189791 / 20000000000) = 1/(10000000000 / 27741189791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14030 : Bounds (1020333211 / 1000000000) (1020333213 / 1000000000) (Real.log (27741189791 / 10000000000)) := by
  have h := reflection_log_14030_neg
  have he : Real.log (27741189791 / 10000000000) = -Real.log (10000000000 / 27741189791) := by
    rw [show ((27741189791 / 10000000000) : ℝ) = ((10000000000 / 27741189791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14031_neg : (514065781 / 500000000) ≤ -Real.log (125000000000 / 349479638181) ∧
    -Real.log (125000000000 / 349479638181) ≤ (257032891 / 250000000) := by
  have h := checkLog_sound (w := (99479638181 / 599479638181)) (n := 12)
    (lo := (167492191 / 500000000)) (hi := (334984383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349479638181 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(349479638181 / 250000000000) = 1/(125000000000 / 349479638181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14031 : Bounds (514065781 / 500000000) (257032891 / 250000000) (Real.log (349479638181 / 125000000000)) := by
  have h := reflection_log_14031_neg
  have he : Real.log (349479638181 / 125000000000) = -Real.log (125000000000 / 349479638181) := by
    rw [show ((349479638181 / 125000000000) : ℝ) = ((125000000000 / 349479638181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14032_neg : (2283484919 / 1000000000) ≤ -Real.log (100000000000 / 981081081081) ∧
    -Real.log (100000000000 / 981081081081) ≤ (2283484923 / 1000000000) := by
  have h := checkLog_sound (w := (181081081081 / 1781081081081)) (n := 12)
    (lo := (204043379 / 1000000000)) (hi := (10202169 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981081081081 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(981081081081 / 800000000000) = 1/(100000000000 / 981081081081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14032 : Bounds (2283484919 / 1000000000) (2283484923 / 1000000000) (Real.log (981081081081 / 100000000000)) := by
  have h := reflection_log_14032_neg
  have he : Real.log (981081081081 / 100000000000) = -Real.log (100000000000 / 981081081081) := by
    rw [show ((981081081081 / 100000000000) : ℝ) = ((100000000000 / 981081081081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14033_neg : (460297117 / 200000000) ≤ -Real.log (250000000000 / 2497252747253) ∧
    -Real.log (250000000000 / 2497252747253) ≤ (2301485589 / 1000000000) := by
  have h := checkLog_sound (w := (497252747253 / 4497252747253)) (n := 12)
    (lo := (44408809 / 200000000)) (hi := (111022023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497252747253 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2497252747253 / 2000000000000) = 1/(250000000000 / 2497252747253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14033 : Bounds (460297117 / 200000000) (2301485589 / 1000000000) (Real.log (2497252747253 / 250000000000)) := by
  have h := reflection_log_14033_neg
  have he : Real.log (2497252747253 / 250000000000) = -Real.log (250000000000 / 2497252747253) := by
    rw [show ((2497252747253 / 250000000000) : ℝ) = ((250000000000 / 2497252747253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14034_neg : (2996929 / 5000000) ≤ -Real.log (1000 / 1821) ∧
    -Real.log (1000 / 1821) ≤ (599385801 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 2821)) (n := 12)
    (lo := (2996929 / 5000000)) (hi := (599385801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1821 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1821 / 1000) = 1/(1000 / 1821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14034 : Bounds (2996929 / 5000000) (599385801 / 1000000000) (Real.log (1821 / 1000)) := by
  have h := reflection_log_14034_neg
  have he : Real.log (1821 / 1000) = -Real.log (1000 / 1821) := by
    rw [show ((1821 / 1000) : ℝ) = ((1000 / 1821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14035_neg : (26880773 / 15625000) ≤ -Real.log (179 / 1000) ∧
    -Real.log (179 / 1000) ≤ (68814779 / 40000000) := by
  have h := checkLog_sound (w := (71 / 429)) (n := 12)
    (lo := (41759389 / 125000000)) (hi := (334075113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 179) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 179) = 1/(179 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14035 : Bounds (-68814779 / 40000000) (-26880773 / 15625000) (Real.log (179 / 1000)) := by
  have h := reflection_log_14035_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14036_neg : (820663 / 1000000000) ≤ -Real.log (1000000 / 1000821) ∧
    -Real.log (1000000 / 1000821) ≤ (102583 / 125000000) := by
  have h := checkLog_sound (w := (821 / 2000821)) (n := 12)
    (lo := (820663 / 1000000000)) (hi := (102583 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000821 / 1000000) = 1/(1000000 / 1000821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14036 : Bounds (820663 / 1000000000) (102583 / 125000000) (Real.log (1000821 / 1000000)) := by
  have h := reflection_log_14036_neg
  have he : Real.log (1000821 / 1000000) = -Real.log (1000000 / 1000821) := by
    rw [show ((1000821 / 1000000) : ℝ) = ((1000000 / 1000821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14037_neg : (821337 / 1000000000) ≤ -Real.log (999179 / 1000000) ∧
    -Real.log (999179 / 1000000) ≤ (410669 / 500000000) := by
  have h := checkLog_sound (w := (821 / 1999179)) (n := 12)
    (lo := (821337 / 1000000000)) (hi := (410669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999179) = 1/(999179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14037 : Bounds (-410669 / 500000000) (-821337 / 1000000000) (Real.log (999179 / 1000000)) := by
  have h := reflection_log_14037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14038_neg : (48365111 / 125000000) ≤ -Real.log (25000 / 36811) ∧
    -Real.log (25000 / 36811) ≤ (386920889 / 1000000000) := by
  have h := checkLog_sound (w := (11811 / 61811)) (n := 12)
    (lo := (48365111 / 125000000)) (hi := (386920889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36811 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36811 / 25000) = 1/(25000 / 36811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14038 : Bounds (48365111 / 125000000) (386920889 / 1000000000) (Real.log (36811 / 25000)) := by
  have h := reflection_log_14038_neg
  have he : Real.log (36811 / 25000) = -Real.log (25000 / 36811) := by
    rw [show ((36811 / 25000) : ℝ) = ((25000 / 36811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14039_neg : (159873169 / 250000000) ≤ -Real.log (13189 / 25000) ∧
    -Real.log (13189 / 25000) ≤ (639492677 / 1000000000) := by
  have h := checkLog_sound (w := (11811 / 38189)) (n := 12)
    (lo := (159873169 / 250000000)) (hi := (639492677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 13189) = 1/(13189 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14039 : Bounds (-639492677 / 1000000000) (-159873169 / 250000000) (Real.log (13189 / 25000)) := by
  have h := reflection_log_14039_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14040_neg : (388986071 / 1000000000) ≤ -Real.log (250000 / 368871) ∧
    -Real.log (250000 / 368871) ≤ (48623259 / 125000000) := by
  have h := checkLog_sound (w := (118871 / 618871)) (n := 12)
    (lo := (388986071 / 1000000000)) (hi := (48623259 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368871 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368871 / 250000) = 1/(250000 / 368871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14040 : Bounds (388986071 / 1000000000) (48623259 / 125000000) (Real.log (368871 / 250000)) := by
  have h := reflection_log_14040_neg
  have he : Real.log (368871 / 250000) = -Real.log (250000 / 368871) := by
    rw [show ((368871 / 250000) : ℝ) = ((250000 / 368871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14041_neg : (322639673 / 500000000) ≤ -Real.log (131129 / 250000) ∧
    -Real.log (131129 / 250000) ≤ (645279347 / 1000000000) := by
  have h := checkLog_sound (w := (118871 / 381129)) (n := 12)
    (lo := (322639673 / 500000000)) (hi := (645279347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 131129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 131129) = 1/(131129 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14041 : Bounds (-645279347 / 1000000000) (-322639673 / 500000000) (Real.log (131129 / 250000)) := by
  have h := reflection_log_14041_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14042_neg : (128146637 / 500000000) ≤ -Real.log (48369685359 / 62500000000) ∧
    -Real.log (48369685359 / 62500000000) ≤ (10251731 / 40000000) := by
  have h := checkLog_sound (w := (14130314641 / 110869685359)) (n := 12)
    (lo := (128146637 / 500000000)) (hi := (10251731 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 48369685359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 48369685359) = 1/(48369685359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14042 : Bounds (-10251731 / 40000000) (-128146637 / 500000000) (Real.log (48369685359 / 62500000000)) := by
  have h := reflection_log_14042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14043_neg : (252571787 / 1000000000) ≤ -Real.log (485500279 / 625000000) ∧
    -Real.log (485500279 / 625000000) ≤ (63142947 / 250000000) := by
  have h := checkLog_sound (w := (139499721 / 1110500279)) (n := 12)
    (lo := (252571787 / 1000000000)) (hi := (63142947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 485500279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 485500279) = 1/(485500279 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14043 : Bounds (-63142947 / 250000000) (-252571787 / 1000000000) (Real.log (485500279 / 625000000)) := by
  have h := reflection_log_14043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14044_neg : (256603391 / 250000000) ≤ -Real.log (5000000000 / 13955189931) ∧
    -Real.log (5000000000 / 13955189931) ≤ (513206783 / 500000000) := by
  have h := checkLog_sound (w := (3955189931 / 23955189931)) (n := 12)
    (lo := (20829149 / 62500000)) (hi := (66653277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13955189931 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(13955189931 / 10000000000) = 1/(5000000000 / 13955189931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14044 : Bounds (256603391 / 250000000) (513206783 / 500000000) (Real.log (13955189931 / 5000000000)) := by
  have h := reflection_log_14044_neg
  have he : Real.log (13955189931 / 5000000000) = -Real.log (5000000000 / 13955189931) := by
    rw [show ((13955189931 / 5000000000) : ℝ) = ((5000000000 / 13955189931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14045_neg : (1034265417 / 1000000000) ≤ -Real.log (2500000000 / 7032597671) ∧
    -Real.log (2500000000 / 7032597671) ≤ (1034265419 / 1000000000) := by
  have h := checkLog_sound (w := (2032597671 / 12032597671)) (n := 12)
    (lo := (341118237 / 1000000000)) (hi := (170559119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7032597671 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7032597671 / 5000000000) = 1/(2500000000 / 7032597671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14045 : Bounds (1034265417 / 1000000000) (1034265419 / 1000000000) (Real.log (7032597671 / 2500000000)) := by
  have h := reflection_log_14045_neg
  have he : Real.log (7032597671 / 2500000000) = -Real.log (2500000000 / 7032597671) := by
    rw [show ((7032597671 / 2500000000) : ℝ) = ((2500000000 / 7032597671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14046_neg : (460297117 / 200000000) ≤ -Real.log (100000000000 / 998901098901) ∧
    -Real.log (100000000000 / 998901098901) ≤ (2301485589 / 1000000000) := by
  have h := checkLog_sound (w := (198901098901 / 1798901098901)) (n := 12)
    (lo := (44408809 / 200000000)) (hi := (111022023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((998901098901 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(998901098901 / 800000000000) = 1/(100000000000 / 998901098901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14046 : Bounds (460297117 / 200000000) (2301485589 / 1000000000) (Real.log (998901098901 / 100000000000)) := by
  have h := reflection_log_14046_neg
  have he : Real.log (998901098901 / 100000000000) = -Real.log (100000000000 / 998901098901) := by
    rw [show ((998901098901 / 100000000000) : ℝ) = ((100000000000 / 998901098901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14047_neg : (289969409 / 125000000) ≤ -Real.log (500000000000 / 5086592178771) ∧
    -Real.log (500000000000 / 5086592178771) ≤ (579938819 / 250000000) := by
  have h := checkLog_sound (w := (1086592178771 / 9086592178771)) (n := 12)
    (lo := (60078433 / 250000000)) (hi := (240313733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5086592178771 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5086592178771 / 4000000000000) = 1/(500000000000 / 5086592178771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14047 : Bounds (289969409 / 125000000) (579938819 / 250000000) (Real.log (5086592178771 / 500000000000)) := by
  have h := reflection_log_14047_neg
  have he : Real.log (5086592178771 / 500000000000) = -Real.log (500000000000 / 5086592178771) := by
    rw [show ((5086592178771 / 500000000000) : ℝ) = ((500000000000 / 5086592178771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14048_neg : (601031891 / 1000000000) ≤ -Real.log (125 / 228) ∧
    -Real.log (125 / 228) ≤ (150257973 / 250000000) := by
  have h := checkLog_sound (w := (103 / 353)) (n := 12)
    (lo := (601031891 / 1000000000)) (hi := (150257973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228 / 125) = 1/(125 / 228) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14048 : Bounds (601031891 / 1000000000) (150257973 / 250000000) (Real.log (228 / 125)) := by
  have h := reflection_log_14048_neg
  have he : Real.log (228 / 125) = -Real.log (125 / 228) := by
    rw [show ((228 / 125) : ℝ) = ((125 / 228) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14049_neg : (868635641 / 500000000) ≤ -Real.log (22 / 125) ∧
    -Real.log (22 / 125) ≤ (347454257 / 200000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 88) = 1/(22 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14049 : Bounds (-347454257 / 200000000) (-868635641 / 500000000) (Real.log (22 / 125)) := by
  have h := reflection_log_14049_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14050_neg : (41183 / 50000000) ≤ -Real.log (125000 / 125103) ∧
    -Real.log (125000 / 125103) ≤ (823661 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 250103)) (n := 12)
    (lo := (41183 / 50000000)) (hi := (823661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125103 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125103 / 125000) = 1/(125000 / 125103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14050 : Bounds (41183 / 50000000) (823661 / 1000000000) (Real.log (125103 / 125000)) := by
  have h := reflection_log_14050_neg
  have he : Real.log (125103 / 125000) = -Real.log (125000 / 125103) := by
    rw [show ((125103 / 125000) : ℝ) = ((125000 / 125103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14051_neg : (824339 / 1000000000) ≤ -Real.log (124897 / 125000) ∧
    -Real.log (124897 / 125000) ≤ (41217 / 50000000) := by
  have h := checkLog_sound (w := (103 / 249897)) (n := 12)
    (lo := (824339 / 1000000000)) (hi := (41217 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124897) = 1/(124897 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14051 : Bounds (-41217 / 50000000) (-824339 / 1000000000) (Real.log (124897 / 125000)) := by
  have h := reflection_log_14051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14052_neg : (97133309 / 250000000) ≤ -Real.log (15625 / 23044) ∧
    -Real.log (15625 / 23044) ≤ (388533237 / 1000000000) := by
  have h := checkLog_sound (w := (7419 / 38669)) (n := 12)
    (lo := (97133309 / 250000000)) (hi := (388533237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23044 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23044 / 15625) = 1/(15625 / 23044) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14052 : Bounds (97133309 / 250000000) (388533237 / 1000000000) (Real.log (23044 / 15625)) := by
  have h := reflection_log_14052_neg
  have he : Real.log (23044 / 15625) = -Real.log (15625 / 23044) := by
    rw [show ((23044 / 15625) : ℝ) = ((15625 / 23044) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14053_neg : (644006601 / 1000000000) ≤ -Real.log (8206 / 15625) ∧
    -Real.log (8206 / 15625) ≤ (322003301 / 500000000) := by
  have h := checkLog_sound (w := (7419 / 23831)) (n := 12)
    (lo := (644006601 / 1000000000)) (hi := (322003301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8206) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 8206) = 1/(8206 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14053 : Bounds (-322003301 / 500000000) (-644006601 / 1000000000) (Real.log (8206 / 15625)) := by
  have h := reflection_log_14053_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14054_neg : (78120643 / 200000000) ≤ -Real.log (62500 / 92367) ∧
    -Real.log (62500 / 92367) ≤ (24412701 / 62500000) := by
  have h := checkLog_sound (w := (29867 / 154867)) (n := 12)
    (lo := (78120643 / 200000000)) (hi := (24412701 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92367 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92367 / 62500) = 1/(62500 / 92367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14054 : Bounds (78120643 / 200000000) (24412701 / 62500000) (Real.log (92367 / 62500)) := by
  have h := reflection_log_14054_neg
  have he : Real.log (92367 / 62500) = -Real.log (62500 / 92367) := by
    rw [show ((92367 / 62500) : ℝ) = ((62500 / 92367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14055_neg : (64984251 / 100000000) ≤ -Real.log (32633 / 62500) ∧
    -Real.log (32633 / 62500) ≤ (649842511 / 1000000000) := by
  have h := checkLog_sound (w := (29867 / 95133)) (n := 12)
    (lo := (64984251 / 100000000)) (hi := (649842511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 32633) = 1/(32633 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14055 : Bounds (-649842511 / 1000000000) (-64984251 / 100000000) (Real.log (32633 / 62500)) := by
  have h := reflection_log_14055_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14056_neg : (51847859 / 200000000) ≤ -Real.log (3014212311 / 3906250000) ∧
    -Real.log (3014212311 / 3906250000) ≤ (2025307 / 7812500) := by
  have h := checkLog_sound (w := (892037689 / 6920462311)) (n := 12)
    (lo := (51847859 / 200000000)) (hi := (2025307 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3014212311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3014212311) = 1/(3014212311 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14056 : Bounds (-2025307 / 7812500) (-51847859 / 200000000) (Real.log (3014212311 / 3906250000)) := by
  have h := reflection_log_14056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14057_neg : (51094673 / 200000000) ≤ -Real.log (189099064 / 244140625) ∧
    -Real.log (189099064 / 244140625) ≤ (127736683 / 500000000) := by
  have h := checkLog_sound (w := (55041561 / 433239689)) (n := 12)
    (lo := (51094673 / 200000000)) (hi := (127736683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 189099064) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 189099064) = 1/(189099064 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14057 : Bounds (-127736683 / 500000000) (-51094673 / 200000000) (Real.log (189099064 / 244140625)) := by
  have h := reflection_log_14057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14058_neg : (1032539837 / 1000000000) ≤ -Real.log (62500000000 / 175511820619) ∧
    -Real.log (62500000000 / 175511820619) ≤ (1032539839 / 1000000000) := by
  have h := checkLog_sound (w := (50511820619 / 300511820619)) (n := 12)
    (lo := (339392657 / 1000000000)) (hi := (169696329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175511820619 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(175511820619 / 125000000000) = 1/(62500000000 / 175511820619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14058 : Bounds (1032539837 / 1000000000) (1032539839 / 1000000000) (Real.log (175511820619 / 62500000000)) := by
  have h := reflection_log_14058_neg
  have he : Real.log (175511820619 / 62500000000) = -Real.log (62500000000 / 175511820619) := by
    rw [show ((175511820619 / 62500000000) : ℝ) = ((62500000000 / 175511820619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14059_neg : (41617829 / 40000000) ≤ -Real.log (500000000000 / 1415239175069) ∧
    -Real.log (500000000000 / 1415239175069) ≤ (1040445727 / 1000000000) := by
  have h := checkLog_sound (w := (415239175069 / 2415239175069)) (n := 12)
    (lo := (69459709 / 200000000)) (hi := (173649273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415239175069 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1415239175069 / 1000000000000) = 1/(500000000000 / 1415239175069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14059 : Bounds (41617829 / 40000000) (1040445727 / 1000000000) (Real.log (1415239175069 / 500000000000)) := by
  have h := reflection_log_14059_neg
  have he : Real.log (1415239175069 / 500000000000) = -Real.log (500000000000 / 1415239175069) := by
    rw [show ((1415239175069 / 500000000000) : ℝ) = ((500000000000 / 1415239175069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14060_neg : (289969409 / 125000000) ≤ -Real.log (50000000000 / 508659217877) ∧
    -Real.log (50000000000 / 508659217877) ≤ (579938819 / 250000000) := by
  have h := checkLog_sound (w := (108659217877 / 908659217877)) (n := 12)
    (lo := (60078433 / 250000000)) (hi := (240313733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508659217877 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(508659217877 / 400000000000) = 1/(50000000000 / 508659217877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14060 : Bounds (289969409 / 125000000) (579938819 / 250000000) (Real.log (508659217877 / 50000000000)) := by
  have h := reflection_log_14060_neg
  have he : Real.log (508659217877 / 50000000000) = -Real.log (50000000000 / 508659217877) := by
    rw [show ((508659217877 / 50000000000) : ℝ) = ((50000000000 / 508659217877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14061_neg : (2338303173 / 1000000000) ≤ -Real.log (500000000000 / 5181818181819) ∧
    -Real.log (500000000000 / 5181818181819) ≤ (2338303177 / 1000000000) := by
  have h := checkLog_sound (w := (1181818181819 / 9181818181819)) (n := 12)
    (lo := (258861633 / 1000000000)) (hi := (129430817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5181818181819 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5181818181819 / 4000000000000) = 1/(500000000000 / 5181818181819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14061 : Bounds (2338303173 / 1000000000) (2338303177 / 1000000000) (Real.log (5181818181819 / 500000000000)) := by
  have h := reflection_log_14061_neg
  have he : Real.log (5181818181819 / 500000000000) = -Real.log (500000000000 / 5181818181819) := by
    rw [show ((5181818181819 / 500000000000) : ℝ) = ((500000000000 / 5181818181819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14062_neg : (602675277 / 1000000000) ≤ -Real.log (1000 / 1827) ∧
    -Real.log (1000 / 1827) ≤ (301337639 / 500000000) := by
  have h := checkLog_sound (w := (827 / 2827)) (n := 12)
    (lo := (602675277 / 1000000000)) (hi := (301337639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827 / 1000) = 1/(1000 / 1827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14062 : Bounds (602675277 / 1000000000) (301337639 / 500000000) (Real.log (1827 / 1000)) := by
  have h := reflection_log_14062_neg
  have he : Real.log (1827 / 1000) = -Real.log (1000 / 1827) := by
    rw [show ((1827 / 1000) : ℝ) = ((1000 / 1827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14063_neg : (1754463683 / 1000000000) ≤ -Real.log (173 / 1000) ∧
    -Real.log (173 / 1000) ≤ (877231843 / 500000000) := by
  have h := checkLog_sound (w := (77 / 423)) (n := 12)
    (lo := (368169323 / 1000000000)) (hi := (92042331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 173) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 173) = 1/(173 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14063 : Bounds (-877231843 / 500000000) (-1754463683 / 1000000000) (Real.log (173 / 1000)) := by
  have h := reflection_log_14063_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14064_neg : (413329 / 500000000) ≤ -Real.log (1000000 / 1000827) ∧
    -Real.log (1000000 / 1000827) ≤ (826659 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 2000827)) (n := 12)
    (lo := (413329 / 500000000)) (hi := (826659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000827 / 1000000) = 1/(1000000 / 1000827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14064 : Bounds (413329 / 500000000) (826659 / 1000000000) (Real.log (1000827 / 1000000)) := by
  have h := reflection_log_14064_neg
  have he : Real.log (1000827 / 1000000) = -Real.log (1000000 / 1000827) := by
    rw [show ((1000827 / 1000000) : ℝ) = ((1000000 / 1000827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14065_neg : (413671 / 500000000) ≤ -Real.log (999173 / 1000000) ∧
    -Real.log (999173 / 1000000) ≤ (827343 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 1999173)) (n := 12)
    (lo := (413671 / 500000000)) (hi := (827343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999173) = 1/(999173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14065 : Bounds (-827343 / 1000000000) (-413671 / 500000000) (Real.log (999173 / 1000000)) := by
  have h := reflection_log_14065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14066_neg : (390151111 / 1000000000) ≤ -Real.log (250000 / 369301) ∧
    -Real.log (250000 / 369301) ≤ (48768889 / 125000000) := by
  have h := checkLog_sound (w := (119301 / 619301)) (n := 12)
    (lo := (390151111 / 1000000000)) (hi := (48768889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369301 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369301 / 250000) = 1/(250000 / 369301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14066 : Bounds (390151111 / 1000000000) (48768889 / 125000000) (Real.log (369301 / 250000)) := by
  have h := reflection_log_14066_neg
  have he : Real.log (369301 / 250000) = -Real.log (250000 / 369301) := by
    rw [show ((369301 / 250000) : ℝ) = ((250000 / 369301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14067_neg : (162140987 / 250000000) ≤ -Real.log (130699 / 250000) ∧
    -Real.log (130699 / 250000) ≤ (648563949 / 1000000000) := by
  have h := checkLog_sound (w := (119301 / 380699)) (n := 12)
    (lo := (162140987 / 250000000)) (hi := (648563949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 130699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 130699) = 1/(130699 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14067 : Bounds (-648563949 / 1000000000) (-162140987 / 250000000) (Real.log (130699 / 250000)) := by
  have h := reflection_log_14067_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14068_neg : (39222653 / 100000000) ≤ -Real.log (1000000 / 1480273) ∧
    -Real.log (1000000 / 1480273) ≤ (392226531 / 1000000000) := by
  have h := checkLog_sound (w := (480273 / 2480273)) (n := 12)
    (lo := (39222653 / 100000000)) (hi := (392226531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1480273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1480273 / 1000000) = 1/(1000000 / 1480273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14068 : Bounds (39222653 / 100000000) (392226531 / 1000000000) (Real.log (1480273 / 1000000)) := by
  have h := reflection_log_14068_neg
  have he : Real.log (1480273 / 1000000) = -Real.log (1000000 / 1480273) := by
    rw [show ((1480273 / 1000000) : ℝ) = ((1000000 / 1480273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14069_neg : (130890321 / 200000000) ≤ -Real.log (519727 / 1000000) ∧
    -Real.log (519727 / 1000000) ≤ (327225803 / 500000000) := by
  have h := checkLog_sound (w := (480273 / 1519727)) (n := 12)
    (lo := (130890321 / 200000000)) (hi := (327225803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 519727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 519727) = 1/(519727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14069 : Bounds (-327225803 / 500000000) (-130890321 / 200000000) (Real.log (519727 / 1000000)) := by
  have h := reflection_log_14069_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14070_neg : (10489003 / 40000000) ≤ -Real.log (769337845471 / 1000000000000) ∧
    -Real.log (769337845471 / 1000000000000) ≤ (65556269 / 250000000) := by
  have h := checkLog_sound (w := (230662154529 / 1769337845471)) (n := 12)
    (lo := (10489003 / 40000000)) (hi := (65556269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 769337845471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 769337845471) = 1/(769337845471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14070 : Bounds (-65556269 / 250000000) (-10489003 / 40000000) (Real.log (769337845471 / 1000000000000)) := by
  have h := reflection_log_14070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14071_neg : (64603209 / 250000000) ≤ -Real.log (48267271399 / 62500000000) ∧
    -Real.log (48267271399 / 62500000000) ≤ (258412837 / 1000000000) := by
  have h := checkLog_sound (w := (14232728601 / 110767271399)) (n := 12)
    (lo := (64603209 / 250000000)) (hi := (258412837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 48267271399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 48267271399) = 1/(48267271399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14071 : Bounds (-258412837 / 1000000000) (-64603209 / 250000000) (Real.log (48267271399 / 62500000000)) := by
  have h := reflection_log_14071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14072_neg : (1038715059 / 1000000000) ≤ -Real.log (31250000000 / 88299499231) ∧
    -Real.log (31250000000 / 88299499231) ≤ (1038715061 / 1000000000) := by
  have h := checkLog_sound (w := (25799499231 / 150799499231)) (n := 12)
    (lo := (345567879 / 1000000000)) (hi := (8639197 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88299499231 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(88299499231 / 62500000000) = 1/(31250000000 / 88299499231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14072 : Bounds (1038715059 / 1000000000) (1038715061 / 1000000000) (Real.log (88299499231 / 31250000000)) := by
  have h := reflection_log_14072_neg
  have he : Real.log (88299499231 / 31250000000) = -Real.log (31250000000 / 88299499231) := by
    rw [show ((88299499231 / 31250000000) : ℝ) = ((31250000000 / 88299499231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14073_neg : (523339067 / 500000000) ≤ -Real.log (500000000000 / 1424087068789) ∧
    -Real.log (500000000000 / 1424087068789) ≤ (130834767 / 125000000) := by
  have h := checkLog_sound (w := (424087068789 / 2424087068789)) (n := 12)
    (lo := (176765477 / 500000000)) (hi := (70706191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1424087068789 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1424087068789 / 1000000000000) = 1/(500000000000 / 1424087068789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14073 : Bounds (523339067 / 500000000) (130834767 / 125000000) (Real.log (1424087068789 / 500000000000)) := by
  have h := reflection_log_14073_neg
  have he : Real.log (1424087068789 / 500000000000) = -Real.log (500000000000 / 1424087068789) := by
    rw [show ((1424087068789 / 500000000000) : ℝ) = ((500000000000 / 1424087068789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14074_neg : (2338303173 / 1000000000) ≤ -Real.log (250000000000 / 2590909090909) ∧
    -Real.log (250000000000 / 2590909090909) ≤ (2338303177 / 1000000000) := by
  have h := checkLog_sound (w := (590909090909 / 4590909090909)) (n := 12)
    (lo := (258861633 / 1000000000)) (hi := (129430817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2590909090909 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2590909090909 / 2000000000000) = 1/(250000000000 / 2590909090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14074 : Bounds (2338303173 / 1000000000) (2338303177 / 1000000000) (Real.log (2590909090909 / 250000000000)) := by
  have h := reflection_log_14074_neg
  have he : Real.log (2590909090909 / 250000000000) = -Real.log (250000000000 / 2590909090909) := by
    rw [show ((2590909090909 / 250000000000) : ℝ) = ((250000000000 / 2590909090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14075_neg : (29464237 / 12500000) ≤ -Real.log (50000000000 / 528034682081) ∧
    -Real.log (50000000000 / 528034682081) ≤ (589284741 / 250000000) := by
  have h := checkLog_sound (w := (128034682081 / 928034682081)) (n := 12)
    (lo := (13884871 / 50000000)) (hi := (277697421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528034682081 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(528034682081 / 400000000000) = 1/(50000000000 / 528034682081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14075 : Bounds (29464237 / 12500000) (589284741 / 250000000) (Real.log (528034682081 / 50000000000)) := by
  have h := reflection_log_14075_neg
  have he : Real.log (528034682081 / 50000000000) = -Real.log (50000000000 / 528034682081) := by
    rw [show ((528034682081 / 50000000000) : ℝ) = ((50000000000 / 528034682081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14076_neg : (302157983 / 500000000) ≤ -Real.log (100 / 183) ∧
    -Real.log (100 / 183) ≤ (604315967 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 283)) (n := 12)
    (lo := (302157983 / 500000000)) (hi := (604315967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183 / 100) = 1/(100 / 183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14076 : Bounds (302157983 / 500000000) (604315967 / 1000000000) (Real.log (183 / 100)) := by
  have h := reflection_log_14076_neg
  have he : Real.log (183 / 100) = -Real.log (100 / 183) := by
    rw [show ((183 / 100) : ℝ) = ((100 / 183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14077_neg : (44298921 / 25000000) ≤ -Real.log (17 / 100) ∧
    -Real.log (17 / 100) ≤ (1771956843 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 21)) (n := 12)
    (lo := (4820781 / 12500000)) (hi := (385662481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 17) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 17) = 1/(17 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14077 : Bounds (-1771956843 / 1000000000) (-44298921 / 25000000) (Real.log (17 / 100)) := by
  have h := reflection_log_14077_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14078_neg : (165931 / 200000000) ≤ -Real.log (100000 / 100083) ∧
    -Real.log (100000 / 100083) ≤ (103707 / 125000000) := by
  have h := checkLog_sound (w := (83 / 200083)) (n := 12)
    (lo := (165931 / 200000000)) (hi := (103707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100083 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100083 / 100000) = 1/(100000 / 100083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14078 : Bounds (165931 / 200000000) (103707 / 125000000) (Real.log (100083 / 100000)) := by
  have h := reflection_log_14078_neg
  have he : Real.log (100083 / 100000) = -Real.log (100000 / 100083) := by
    rw [show ((100083 / 100000) : ℝ) = ((100000 / 100083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14079_neg : (103793 / 125000000) ≤ -Real.log (99917 / 100000) ∧
    -Real.log (99917 / 100000) ≤ (166069 / 200000000) := by
  have h := checkLog_sound (w := (83 / 199917)) (n := 12)
    (lo := (103793 / 125000000)) (hi := (166069 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99917) = 1/(99917 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14079 : Bounds (-166069 / 200000000) (-103793 / 125000000) (Real.log (99917 / 100000)) := by
  have h := reflection_log_14079_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


