-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0027__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0027__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T04:33:20.234731+00:00
-- url     : https://prove2.me/theorems/2d0ff9b9-a18a-4956-a347-30525d9a6e9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0027 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0028)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0027 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0028)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0027 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0028)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0027 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0028) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0027 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0028).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0027 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1728_neg : (85309553 / 1000000000) ≤ -Real.log (229557 / 250000) ∧
    -Real.log (229557 / 250000) ≤ (42654777 / 500000000) := by
  have h := checkLog_sound (w := (20443 / 479557)) (n := 12)
    (lo := (85309553 / 1000000000)) (hi := (42654777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229557) = 1/(229557 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1728 : Bounds (-42654777 / 500000000) (-85309553 / 1000000000) (Real.log (229557 / 250000)) := by
  have h := reflection_log_1728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1729_neg : (1341823 / 200000000) ≤ -Real.log (62082083751 / 62500000000) ∧
    -Real.log (62082083751 / 62500000000) ≤ (1677279 / 250000000) := by
  have h := checkLog_sound (w := (417916249 / 124582083751)) (n := 12)
    (lo := (1341823 / 200000000)) (hi := (1677279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62082083751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62082083751) = 1/(62082083751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1729 : Bounds (-1677279 / 250000000) (-1341823 / 200000000) (Real.log (62082083751 / 62500000000)) := by
  have h := reflection_log_1729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1730_neg : (1668523 / 250000000) ≤ -Real.log (993348129519 / 1000000000000) ∧
    -Real.log (993348129519 / 1000000000000) ≤ (6674093 / 1000000000) := by
  have h := checkLog_sound (w := (6651870481 / 1993348129519)) (n := 12)
    (lo := (1668523 / 250000000)) (hi := (6674093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993348129519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993348129519) = 1/(993348129519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1730 : Bounds (-6674093 / 1000000000) (-1668523 / 250000000) (Real.log (993348129519 / 1000000000000)) := by
  have h := reflection_log_1730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1731_neg : (16348113 / 100000000) ≤ -Real.log (500000000000 / 588801567003) ∧
    -Real.log (500000000000 / 588801567003) ≤ (163481131 / 1000000000) := by
  have h := checkLog_sound (w := (88801567003 / 1088801567003)) (n := 12)
    (lo := (16348113 / 100000000)) (hi := (163481131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588801567003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588801567003 / 500000000000) = 1/(500000000000 / 588801567003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1731 : Bounds (16348113 / 100000000) (163481131 / 1000000000) (Real.log (588801567003 / 500000000000)) := by
  have h := reflection_log_1731_neg
  have he : Real.log (588801567003 / 500000000000) = -Real.log (500000000000 / 588801567003) := by
    rw [show ((588801567003 / 500000000000) : ℝ) = ((500000000000 / 588801567003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1732_neg : (16390999 / 100000000) ≤ -Real.log (500000000000 / 589054134703) ∧
    -Real.log (500000000000 / 589054134703) ≤ (163909991 / 1000000000) := by
  have h := checkLog_sound (w := (89054134703 / 1089054134703)) (n := 12)
    (lo := (16390999 / 100000000)) (hi := (163909991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589054134703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589054134703 / 500000000000) = 1/(500000000000 / 589054134703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1732 : Bounds (16390999 / 100000000) (163909991 / 1000000000) (Real.log (589054134703 / 500000000000)) := by
  have h := reflection_log_1732_neg
  have he : Real.log (589054134703 / 500000000000) = -Real.log (500000000000 / 589054134703) := by
    rw [show ((589054134703 / 500000000000) : ℝ) = ((500000000000 / 589054134703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1733_neg : (327906873 / 1000000000) ≤ -Real.log (250000000000 / 347014925373) ∧
    -Real.log (250000000000 / 347014925373) ≤ (163953437 / 500000000) := by
  have h := checkLog_sound (w := (97014925373 / 597014925373)) (n := 12)
    (lo := (327906873 / 1000000000)) (hi := (163953437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347014925373 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347014925373 / 250000000000) = 1/(250000000000 / 347014925373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1733 : Bounds (327906873 / 1000000000) (163953437 / 500000000) (Real.log (347014925373 / 250000000000)) := by
  have h := reflection_log_1733_neg
  have he : Real.log (347014925373 / 250000000000) = -Real.log (250000000000 / 347014925373) := by
    rw [show ((347014925373 / 250000000000) : ℝ) = ((250000000000 / 347014925373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1734_neg : (328112301 / 1000000000) ≤ -Real.log (500000000000 / 694172438501) ∧
    -Real.log (500000000000 / 694172438501) ≤ (164056151 / 500000000) := by
  have h := checkLog_sound (w := (194172438501 / 1194172438501)) (n := 12)
    (lo := (328112301 / 1000000000)) (hi := (164056151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694172438501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694172438501 / 500000000000) = 1/(500000000000 / 694172438501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1734 : Bounds (328112301 / 1000000000) (164056151 / 500000000) (Real.log (694172438501 / 500000000000)) := by
  have h := reflection_log_1734_neg
  have he : Real.log (694172438501 / 500000000000) = -Real.log (500000000000 / 694172438501) := by
    rw [show ((694172438501 / 500000000000) : ℝ) = ((500000000000 / 694172438501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1735_neg : (75372443 / 500000000) ≤ -Real.log (10000 / 11627) ∧
    -Real.log (10000 / 11627) ≤ (150744887 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 21627)) (n := 12)
    (lo := (75372443 / 500000000)) (hi := (150744887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11627 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11627 / 10000) = 1/(10000 / 11627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1735 : Bounds (75372443 / 500000000) (150744887 / 1000000000) (Real.log (11627 / 10000)) := by
  have h := reflection_log_1735_neg
  have he : Real.log (11627 / 10000) = -Real.log (10000 / 11627) := by
    rw [show ((11627 / 10000) : ℝ) = ((10000 / 11627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1736_neg : (177572849 / 1000000000) ≤ -Real.log (8373 / 10000) ∧
    -Real.log (8373 / 10000) ≤ (3551457 / 20000000) := by
  have h := checkLog_sound (w := (1627 / 18373)) (n := 12)
    (lo := (177572849 / 1000000000)) (hi := (3551457 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8373) = 1/(8373 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1736 : Bounds (-3551457 / 20000000) (-177572849 / 1000000000) (Real.log (8373 / 10000)) := by
  have h := reflection_log_1736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1737_neg : (81343 / 500000000) ≤ -Real.log (10000000 / 10001627) ∧
    -Real.log (10000000 / 10001627) ≤ (162687 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 20001627)) (n := 12)
    (lo := (81343 / 500000000)) (hi := (162687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001627 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001627 / 10000000) = 1/(10000000 / 10001627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1737 : Bounds (81343 / 500000000) (162687 / 1000000000) (Real.log (10001627 / 10000000)) := by
  have h := reflection_log_1737_neg
  have he : Real.log (10001627 / 10000000) = -Real.log (10000000 / 10001627) := by
    rw [show ((10001627 / 10000000) : ℝ) = ((10000000 / 10001627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1738_neg : (162713 / 1000000000) ≤ -Real.log (9998373 / 10000000) ∧
    -Real.log (9998373 / 10000000) ≤ (81357 / 500000000) := by
  have h := checkLog_sound (w := (1627 / 19998373)) (n := 12)
    (lo := (162713 / 1000000000)) (hi := (81357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998373) = 1/(9998373 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1738 : Bounds (-81357 / 500000000) (-162713 / 1000000000) (Real.log (9998373 / 10000000)) := by
  have h := reflection_log_1738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1739_neg : (78449747 / 1000000000) ≤ -Real.log (1000000 / 1081609) ∧
    -Real.log (1000000 / 1081609) ≤ (19612437 / 250000000) := by
  have h := checkLog_sound (w := (81609 / 2081609)) (n := 12)
    (lo := (78449747 / 1000000000)) (hi := (19612437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081609 / 1000000) = 1/(1000000 / 1081609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1739 : Bounds (78449747 / 1000000000) (19612437 / 250000000) (Real.log (1081609 / 1000000)) := by
  have h := reflection_log_1739_neg
  have he : Real.log (1081609 / 1000000) = -Real.log (1000000 / 1081609) := by
    rw [show ((1081609 / 1000000) : ℝ) = ((1000000 / 1081609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1740_neg : (85132053 / 1000000000) ≤ -Real.log (918391 / 1000000) ∧
    -Real.log (918391 / 1000000) ≤ (42566027 / 500000000) := by
  have h := checkLog_sound (w := (81609 / 1918391)) (n := 12)
    (lo := (85132053 / 1000000000)) (hi := (42566027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918391) = 1/(918391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1740 : Bounds (-42566027 / 500000000) (-85132053 / 1000000000) (Real.log (918391 / 1000000)) := by
  have h := reflection_log_1740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1741_neg : (78647581 / 1000000000) ≤ -Real.log (1000000 / 1081823) ∧
    -Real.log (1000000 / 1081823) ≤ (39323791 / 500000000) := by
  have h := checkLog_sound (w := (81823 / 2081823)) (n := 12)
    (lo := (78647581 / 1000000000)) (hi := (39323791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081823 / 1000000) = 1/(1000000 / 1081823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1741 : Bounds (78647581 / 1000000000) (39323791 / 500000000) (Real.log (1081823 / 1000000)) := by
  have h := reflection_log_1741_neg
  have he : Real.log (1081823 / 1000000) = -Real.log (1000000 / 1081823) := by
    rw [show ((1081823 / 1000000) : ℝ) = ((1000000 / 1081823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1742_neg : (10670637 / 125000000) ≤ -Real.log (918177 / 1000000) ∧
    -Real.log (918177 / 1000000) ≤ (85365097 / 1000000000) := by
  have h := checkLog_sound (w := (81823 / 1918177)) (n := 12)
    (lo := (10670637 / 125000000)) (hi := (85365097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918177) = 1/(918177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1742 : Bounds (-85365097 / 1000000000) (-10670637 / 125000000) (Real.log (918177 / 1000000)) := by
  have h := reflection_log_1742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1743_neg : (1343503 / 200000000) ≤ -Real.log (993304996671 / 1000000000000) ∧
    -Real.log (993304996671 / 1000000000000) ≤ (1679379 / 250000000) := by
  have h := checkLog_sound (w := (6695003329 / 1993304996671)) (n := 12)
    (lo := (1343503 / 200000000)) (hi := (1679379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993304996671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993304996671) = 1/(993304996671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1743 : Bounds (-1679379 / 250000000) (-1343503 / 200000000) (Real.log (993304996671 / 1000000000000)) := by
  have h := reflection_log_1743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1744_neg : (1336461 / 200000000) ≤ -Real.log (993339971119 / 1000000000000) ∧
    -Real.log (993339971119 / 1000000000000) ≤ (3341153 / 500000000) := by
  have h := checkLog_sound (w := (6660028881 / 1993339971119)) (n := 12)
    (lo := (1336461 / 200000000)) (hi := (3341153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993339971119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993339971119) = 1/(993339971119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1744 : Bounds (-3341153 / 500000000) (-1336461 / 200000000) (Real.log (993339971119 / 1000000000000)) := by
  have h := reflection_log_1744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1745_neg : (817909 / 5000000) ≤ -Real.log (3906250000 / 4600475349) ∧
    -Real.log (3906250000 / 4600475349) ≤ (163581801 / 1000000000) := by
  have h := checkLog_sound (w := (694225349 / 8506725349)) (n := 12)
    (lo := (817909 / 5000000)) (hi := (163581801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4600475349 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4600475349 / 3906250000) = 1/(3906250000 / 4600475349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1745 : Bounds (817909 / 5000000) (163581801 / 1000000000) (Real.log (4600475349 / 3906250000)) := by
  have h := reflection_log_1745_neg
  have he : Real.log (4600475349 / 3906250000) = -Real.log (3906250000 / 4600475349) := by
    rw [show ((4600475349 / 3906250000) : ℝ) = ((3906250000 / 4600475349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1746_neg : (164012677 / 1000000000) ≤ -Real.log (244140625 / 287653626) ∧
    -Real.log (244140625 / 287653626) ≤ (82006339 / 500000000) := by
  have h := checkLog_sound (w := (43513001 / 531794251)) (n := 12)
    (lo := (164012677 / 1000000000)) (hi := (82006339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287653626 / 244140625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287653626 / 244140625) = 1/(244140625 / 287653626) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1746 : Bounds (164012677 / 1000000000) (82006339 / 500000000) (Real.log (287653626 / 244140625)) := by
  have h := reflection_log_1746_neg
  have he : Real.log (287653626 / 244140625) = -Real.log (244140625 / 287653626) := by
    rw [show ((287653626 / 244140625) : ℝ) = ((244140625 / 287653626) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1747_neg : (328112301 / 1000000000) ≤ -Real.log (1000000000 / 1388344877) ∧
    -Real.log (1000000000 / 1388344877) ≤ (164056151 / 500000000) := by
  have h := checkLog_sound (w := (388344877 / 2388344877)) (n := 12)
    (lo := (328112301 / 1000000000)) (hi := (164056151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1388344877 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1388344877 / 1000000000) = 1/(1000000000 / 1388344877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1747 : Bounds (328112301 / 1000000000) (164056151 / 500000000) (Real.log (1388344877 / 1000000000)) := by
  have h := reflection_log_1747_neg
  have he : Real.log (1388344877 / 1000000000) = -Real.log (1000000000 / 1388344877) := by
    rw [show ((1388344877 / 1000000000) : ℝ) = ((1000000000 / 1388344877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1748_neg : (41039717 / 125000000) ≤ -Real.log (500000000000 / 694315060313) ∧
    -Real.log (500000000000 / 694315060313) ≤ (328317737 / 1000000000) := by
  have h := checkLog_sound (w := (194315060313 / 1194315060313)) (n := 12)
    (lo := (41039717 / 125000000)) (hi := (328317737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694315060313 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694315060313 / 500000000000) = 1/(500000000000 / 694315060313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1748 : Bounds (41039717 / 125000000) (328317737 / 1000000000) (Real.log (694315060313 / 500000000000)) := by
  have h := reflection_log_1748_neg
  have he : Real.log (694315060313 / 500000000000) = -Real.log (500000000000 / 694315060313) := by
    rw [show ((694315060313 / 500000000000) : ℝ) = ((500000000000 / 694315060313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1749_neg : (150830889 / 1000000000) ≤ -Real.log (2500 / 2907) ∧
    -Real.log (2500 / 2907) ≤ (15083089 / 100000000) := by
  have h := checkLog_sound (w := (407 / 5407)) (n := 12)
    (lo := (150830889 / 1000000000)) (hi := (15083089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2907 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2907 / 2500) = 1/(2500 / 2907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1749 : Bounds (150830889 / 1000000000) (15083089 / 100000000) (Real.log (2907 / 2500)) := by
  have h := reflection_log_1749_neg
  have he : Real.log (2907 / 2500) = -Real.log (2500 / 2907) := by
    rw [show ((2907 / 2500) : ℝ) = ((2500 / 2907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1750_neg : (1388221 / 7812500) ≤ -Real.log (2093 / 2500) ∧
    -Real.log (2093 / 2500) ≤ (177692289 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 4593)) (n := 12)
    (lo := (1388221 / 7812500)) (hi := (177692289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2093) = 1/(2093 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1750 : Bounds (-177692289 / 1000000000) (-1388221 / 7812500) (Real.log (2093 / 2500)) := by
  have h := reflection_log_1750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1751_neg : (81393 / 500000000) ≤ -Real.log (2500000 / 2500407) ∧
    -Real.log (2500000 / 2500407) ≤ (162787 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 5000407)) (n := 12)
    (lo := (81393 / 500000000)) (hi := (162787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500407 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500407 / 2500000) = 1/(2500000 / 2500407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1751 : Bounds (81393 / 500000000) (162787 / 1000000000) (Real.log (2500407 / 2500000)) := by
  have h := reflection_log_1751_neg
  have he : Real.log (2500407 / 2500000) = -Real.log (2500000 / 2500407) := by
    rw [show ((2500407 / 2500000) : ℝ) = ((2500000 / 2500407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1752_neg : (162813 / 1000000000) ≤ -Real.log (2499593 / 2500000) ∧
    -Real.log (2499593 / 2500000) ≤ (81407 / 500000000) := by
  have h := checkLog_sound (w := (407 / 4999593)) (n := 12)
    (lo := (162813 / 1000000000)) (hi := (81407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499593) = 1/(2499593 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1752 : Bounds (-81407 / 500000000) (-162813 / 1000000000) (Real.log (2499593 / 2500000)) := by
  have h := reflection_log_1752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1753_neg : (39248449 / 500000000) ≤ -Real.log (50000 / 54083) ∧
    -Real.log (50000 / 54083) ≤ (78496899 / 1000000000) := by
  have h := checkLog_sound (w := (4083 / 104083)) (n := 12)
    (lo := (39248449 / 500000000)) (hi := (78496899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54083 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54083 / 50000) = 1/(50000 / 54083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1753 : Bounds (39248449 / 500000000) (78496899 / 1000000000) (Real.log (54083 / 50000)) := by
  have h := reflection_log_1753_neg
  have he : Real.log (54083 / 50000) = -Real.log (50000 / 54083) := by
    rw [show ((54083 / 50000) : ℝ) = ((50000 / 54083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1754_neg : (42593793 / 500000000) ≤ -Real.log (45917 / 50000) ∧
    -Real.log (45917 / 50000) ≤ (85187587 / 1000000000) := by
  have h := checkLog_sound (w := (4083 / 95917)) (n := 12)
    (lo := (42593793 / 500000000)) (hi := (85187587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45917) = 1/(45917 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1754 : Bounds (-85187587 / 1000000000) (-42593793 / 500000000) (Real.log (45917 / 50000)) := by
  have h := reflection_log_1754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1755_neg : (39347361 / 500000000) ≤ -Real.log (500000 / 540937) ∧
    -Real.log (500000 / 540937) ≤ (78694723 / 1000000000) := by
  have h := checkLog_sound (w := (40937 / 1040937)) (n := 12)
    (lo := (39347361 / 500000000)) (hi := (78694723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540937 / 500000) = 1/(500000 / 540937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1755 : Bounds (39347361 / 500000000) (78694723 / 1000000000) (Real.log (540937 / 500000)) := by
  have h := reflection_log_1755_neg
  have he : Real.log (540937 / 500000) = -Real.log (500000 / 540937) := by
    rw [show ((540937 / 500000) : ℝ) = ((500000 / 540937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1756_neg : (42710321 / 500000000) ≤ -Real.log (459063 / 500000) ∧
    -Real.log (459063 / 500000) ≤ (85420643 / 1000000000) := by
  have h := checkLog_sound (w := (40937 / 959063)) (n := 12)
    (lo := (42710321 / 500000000)) (hi := (85420643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459063) = 1/(459063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1756 : Bounds (-85420643 / 1000000000) (-42710321 / 500000000) (Real.log (459063 / 500000)) := by
  have h := reflection_log_1756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1757_neg : (42037 / 6250000) ≤ -Real.log (248324162031 / 250000000000) ∧
    -Real.log (248324162031 / 250000000000) ≤ (6725921 / 1000000000) := by
  have h := checkLog_sound (w := (1675837969 / 498324162031)) (n := 12)
    (lo := (42037 / 6250000)) (hi := (6725921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248324162031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248324162031) = 1/(248324162031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1757 : Bounds (-6725921 / 1000000000) (-42037 / 6250000) (Real.log (248324162031 / 250000000000)) := by
  have h := reflection_log_1757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1758_neg : (52271 / 7812500) ≤ -Real.log (2483329111 / 2500000000) ∧
    -Real.log (2483329111 / 2500000000) ≤ (6690689 / 1000000000) := by
  have h := checkLog_sound (w := (16670889 / 4983329111)) (n := 12)
    (lo := (52271 / 7812500)) (hi := (6690689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2483329111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2483329111) = 1/(2483329111 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1758 : Bounds (-6690689 / 1000000000) (-52271 / 7812500) (Real.log (2483329111 / 2500000000)) := by
  have h := reflection_log_1758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1759_neg : (40921121 / 250000000) ≤ -Real.log (100000000000 / 117784262909) ∧
    -Real.log (100000000000 / 117784262909) ≤ (32736897 / 200000000) := by
  have h := checkLog_sound (w := (17784262909 / 217784262909)) (n := 12)
    (lo := (40921121 / 250000000)) (hi := (32736897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117784262909 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117784262909 / 100000000000) = 1/(100000000000 / 117784262909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1759 : Bounds (40921121 / 250000000) (32736897 / 200000000) (Real.log (117784262909 / 100000000000)) := by
  have h := reflection_log_1759_neg
  have he : Real.log (117784262909 / 100000000000) = -Real.log (100000000000 / 117784262909) := by
    rw [show ((117784262909 / 100000000000) : ℝ) = ((100000000000 / 117784262909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1760_neg : (32823073 / 200000000) ≤ -Real.log (31250000000 / 36823445257) ∧
    -Real.log (31250000000 / 36823445257) ≤ (82057683 / 500000000) := by
  have h := checkLog_sound (w := (5573445257 / 68073445257)) (n := 12)
    (lo := (32823073 / 200000000)) (hi := (82057683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36823445257 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36823445257 / 31250000000) = 1/(31250000000 / 36823445257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1760 : Bounds (32823073 / 200000000) (82057683 / 500000000) (Real.log (36823445257 / 31250000000)) := by
  have h := reflection_log_1760_neg
  have he : Real.log (36823445257 / 31250000000) = -Real.log (31250000000 / 36823445257) := by
    rw [show ((36823445257 / 31250000000) : ℝ) = ((31250000000 / 36823445257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1761_neg : (41039717 / 125000000) ≤ -Real.log (62500000000 / 86789382539) ∧
    -Real.log (62500000000 / 86789382539) ≤ (328317737 / 1000000000) := by
  have h := checkLog_sound (w := (24289382539 / 149289382539)) (n := 12)
    (lo := (41039717 / 125000000)) (hi := (328317737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86789382539 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86789382539 / 62500000000) = 1/(62500000000 / 86789382539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1761 : Bounds (41039717 / 125000000) (328317737 / 1000000000) (Real.log (86789382539 / 62500000000)) := by
  have h := reflection_log_1761_neg
  have he : Real.log (86789382539 / 62500000000) = -Real.log (62500000000 / 86789382539) := by
    rw [show ((86789382539 / 62500000000) : ℝ) = ((62500000000 / 86789382539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1762_neg : (164261589 / 500000000) ≤ -Real.log (500000000000 / 694457716197) ∧
    -Real.log (500000000000 / 694457716197) ≤ (328523179 / 1000000000) := by
  have h := checkLog_sound (w := (194457716197 / 1194457716197)) (n := 12)
    (lo := (164261589 / 500000000)) (hi := (328523179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694457716197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694457716197 / 500000000000) = 1/(500000000000 / 694457716197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1762 : Bounds (164261589 / 500000000) (328523179 / 1000000000) (Real.log (694457716197 / 500000000000)) := by
  have h := reflection_log_1762_neg
  have he : Real.log (694457716197 / 500000000000) = -Real.log (500000000000 / 694457716197) := by
    rw [show ((694457716197 / 500000000000) : ℝ) = ((500000000000 / 694457716197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1763_neg : (30183377 / 200000000) ≤ -Real.log (10000 / 11629) ∧
    -Real.log (10000 / 11629) ≤ (75458443 / 500000000) := by
  have h := checkLog_sound (w := (1629 / 21629)) (n := 12)
    (lo := (30183377 / 200000000)) (hi := (75458443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11629 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11629 / 10000) = 1/(10000 / 11629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1763 : Bounds (30183377 / 200000000) (75458443 / 500000000) (Real.log (11629 / 10000)) := by
  have h := reflection_log_1763_neg
  have he : Real.log (11629 / 10000) = -Real.log (10000 / 11629) := by
    rw [show ((11629 / 10000) : ℝ) = ((10000 / 11629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1764_neg : (177811741 / 1000000000) ≤ -Real.log (8371 / 10000) ∧
    -Real.log (8371 / 10000) ≤ (88905871 / 500000000) := by
  have h := checkLog_sound (w := (1629 / 18371)) (n := 12)
    (lo := (177811741 / 1000000000)) (hi := (88905871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8371) = 1/(8371 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1764 : Bounds (-88905871 / 500000000) (-177811741 / 1000000000) (Real.log (8371 / 10000)) := by
  have h := reflection_log_1764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1765_neg : (81443 / 500000000) ≤ -Real.log (10000000 / 10001629) ∧
    -Real.log (10000000 / 10001629) ≤ (162887 / 1000000000) := by
  have h := checkLog_sound (w := (1629 / 20001629)) (n := 12)
    (lo := (81443 / 500000000)) (hi := (162887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001629 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001629 / 10000000) = 1/(10000000 / 10001629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1765 : Bounds (81443 / 500000000) (162887 / 1000000000) (Real.log (10001629 / 10000000)) := by
  have h := reflection_log_1765_neg
  have he : Real.log (10001629 / 10000000) = -Real.log (10000000 / 10001629) := by
    rw [show ((10001629 / 10000000) : ℝ) = ((10000000 / 10001629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1766_neg : (162913 / 1000000000) ≤ -Real.log (9998371 / 10000000) ∧
    -Real.log (9998371 / 10000000) ≤ (81457 / 500000000) := by
  have h := checkLog_sound (w := (1629 / 19998371)) (n := 12)
    (lo := (162913 / 1000000000)) (hi := (81457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998371) = 1/(9998371 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1766 : Bounds (-81457 / 500000000) (-162913 / 1000000000) (Real.log (9998371 / 10000000)) := by
  have h := reflection_log_1766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1767_neg : (39272023 / 500000000) ≤ -Real.log (1000000 / 1081711) ∧
    -Real.log (1000000 / 1081711) ≤ (78544047 / 1000000000) := by
  have h := checkLog_sound (w := (81711 / 2081711)) (n := 12)
    (lo := (39272023 / 500000000)) (hi := (78544047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081711 / 1000000) = 1/(1000000 / 1081711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1767 : Bounds (39272023 / 500000000) (78544047 / 1000000000) (Real.log (1081711 / 1000000)) := by
  have h := reflection_log_1767_neg
  have he : Real.log (1081711 / 1000000) = -Real.log (1000000 / 1081711) := by
    rw [show ((1081711 / 1000000) : ℝ) = ((1000000 / 1081711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1768_neg : (85243123 / 1000000000) ≤ -Real.log (918289 / 1000000) ∧
    -Real.log (918289 / 1000000) ≤ (21310781 / 250000000) := by
  have h := checkLog_sound (w := (81711 / 1918289)) (n := 12)
    (lo := (85243123 / 1000000000)) (hi := (21310781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918289) = 1/(918289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1768 : Bounds (-21310781 / 250000000) (-85243123 / 1000000000) (Real.log (918289 / 1000000)) := by
  have h := reflection_log_1768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1769_neg : (78740937 / 1000000000) ≤ -Real.log (250000 / 270481) ∧
    -Real.log (250000 / 270481) ≤ (39370469 / 500000000) := by
  have h := checkLog_sound (w := (20481 / 520481)) (n := 12)
    (lo := (78740937 / 1000000000)) (hi := (39370469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270481 / 250000) = 1/(250000 / 270481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1769 : Bounds (78740937 / 1000000000) (39370469 / 500000000) (Real.log (270481 / 250000)) := by
  have h := reflection_log_1769_neg
  have he : Real.log (270481 / 250000) = -Real.log (250000 / 270481) := by
    rw [show ((270481 / 250000) : ℝ) = ((250000 / 270481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1770_neg : (85475103 / 1000000000) ≤ -Real.log (229519 / 250000) ∧
    -Real.log (229519 / 250000) ≤ (2671097 / 31250000) := by
  have h := checkLog_sound (w := (20481 / 479519)) (n := 12)
    (lo := (85475103 / 1000000000)) (hi := (2671097 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229519) = 1/(229519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1770 : Bounds (-2671097 / 31250000) (-85475103 / 1000000000) (Real.log (229519 / 250000)) := by
  have h := reflection_log_1770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1771_neg : (1346833 / 200000000) ≤ -Real.log (62080528639 / 62500000000) ∧
    -Real.log (62080528639 / 62500000000) ≤ (3367083 / 500000000) := by
  have h := checkLog_sound (w := (419471361 / 124580528639)) (n := 12)
    (lo := (1346833 / 200000000)) (hi := (3367083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62080528639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62080528639) = 1/(62080528639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1771 : Bounds (-3367083 / 500000000) (-1346833 / 200000000) (Real.log (62080528639 / 62500000000)) := by
  have h := reflection_log_1771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1772_neg : (1674769 / 250000000) ≤ -Real.log (993323312479 / 1000000000000) ∧
    -Real.log (993323312479 / 1000000000000) ≤ (6699077 / 1000000000) := by
  have h := checkLog_sound (w := (6676687521 / 1993323312479)) (n := 12)
    (lo := (1674769 / 250000000)) (hi := (6699077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993323312479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993323312479) = 1/(993323312479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1772 : Bounds (-6699077 / 1000000000) (-1674769 / 250000000) (Real.log (993323312479 / 1000000000000)) := by
  have h := reflection_log_1772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1773_neg : (163787169 / 1000000000) ≤ -Real.log (100000000000 / 117796358227) ∧
    -Real.log (100000000000 / 117796358227) ≤ (16378717 / 100000000) := by
  have h := checkLog_sound (w := (17796358227 / 217796358227)) (n := 12)
    (lo := (163787169 / 1000000000)) (hi := (16378717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117796358227 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117796358227 / 100000000000) = 1/(100000000000 / 117796358227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1773 : Bounds (163787169 / 1000000000) (16378717 / 100000000) (Real.log (117796358227 / 100000000000)) := by
  have h := reflection_log_1773_neg
  have he : Real.log (117796358227 / 100000000000) = -Real.log (100000000000 / 117796358227) := by
    rw [show ((117796358227 / 100000000000) : ℝ) = ((100000000000 / 117796358227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1774_neg : (4105401 / 25000000) ≤ -Real.log (100000000000 / 117846888493) ∧
    -Real.log (100000000000 / 117846888493) ≤ (164216041 / 1000000000) := by
  have h := checkLog_sound (w := (17846888493 / 217846888493)) (n := 12)
    (lo := (4105401 / 25000000)) (hi := (164216041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117846888493 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117846888493 / 100000000000) = 1/(100000000000 / 117846888493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1774 : Bounds (4105401 / 25000000) (164216041 / 1000000000) (Real.log (117846888493 / 100000000000)) := by
  have h := reflection_log_1774_neg
  have he : Real.log (117846888493 / 100000000000) = -Real.log (100000000000 / 117846888493) := by
    rw [show ((117846888493 / 100000000000) : ℝ) = ((100000000000 / 117846888493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1775_neg : (164261589 / 500000000) ≤ -Real.log (125000000000 / 173614429049) ∧
    -Real.log (125000000000 / 173614429049) ≤ (328523179 / 1000000000) := by
  have h := checkLog_sound (w := (48614429049 / 298614429049)) (n := 12)
    (lo := (164261589 / 500000000)) (hi := (328523179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173614429049 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173614429049 / 125000000000) = 1/(125000000000 / 173614429049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1775 : Bounds (164261589 / 500000000) (328523179 / 1000000000) (Real.log (173614429049 / 125000000000)) := by
  have h := reflection_log_1775_neg
  have he : Real.log (173614429049 / 125000000000) = -Real.log (125000000000 / 173614429049) := by
    rw [show ((173614429049 / 125000000000) : ℝ) = ((125000000000 / 173614429049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1776_neg : (164364313 / 500000000) ≤ -Real.log (100000000000 / 138920081233) ∧
    -Real.log (100000000000 / 138920081233) ≤ (328728627 / 1000000000) := by
  have h := checkLog_sound (w := (38920081233 / 238920081233)) (n := 12)
    (lo := (164364313 / 500000000)) (hi := (328728627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138920081233 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138920081233 / 100000000000) = 1/(100000000000 / 138920081233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1776 : Bounds (164364313 / 500000000) (328728627 / 1000000000) (Real.log (138920081233 / 100000000000)) := by
  have h := reflection_log_1776_neg
  have he : Real.log (138920081233 / 100000000000) = -Real.log (100000000000 / 138920081233) := by
    rw [show ((138920081233 / 100000000000) : ℝ) = ((100000000000 / 138920081233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1777_neg : (151002873 / 1000000000) ≤ -Real.log (1000 / 1163) ∧
    -Real.log (1000 / 1163) ≤ (75501437 / 500000000) := by
  have h := checkLog_sound (w := (163 / 2163)) (n := 12)
    (lo := (151002873 / 1000000000)) (hi := (75501437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163 / 1000) = 1/(1000 / 1163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1777 : Bounds (151002873 / 1000000000) (75501437 / 500000000) (Real.log (1163 / 1000)) := by
  have h := reflection_log_1777_neg
  have he : Real.log (1163 / 1000) = -Real.log (1000 / 1163) := by
    rw [show ((1163 / 1000) : ℝ) = ((1000 / 1163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1778_neg : (22241401 / 125000000) ≤ -Real.log (837 / 1000) ∧
    -Real.log (837 / 1000) ≤ (177931209 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1837)) (n := 12)
    (lo := (22241401 / 125000000)) (hi := (177931209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 837) = 1/(837 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1778 : Bounds (-177931209 / 1000000000) (-22241401 / 125000000) (Real.log (837 / 1000)) := by
  have h := reflection_log_1778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1779_neg : (81493 / 500000000) ≤ -Real.log (1000000 / 1000163) ∧
    -Real.log (1000000 / 1000163) ≤ (162987 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 2000163)) (n := 12)
    (lo := (81493 / 500000000)) (hi := (162987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000163 / 1000000) = 1/(1000000 / 1000163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1779 : Bounds (81493 / 500000000) (162987 / 1000000000) (Real.log (1000163 / 1000000)) := by
  have h := reflection_log_1779_neg
  have he : Real.log (1000163 / 1000000) = -Real.log (1000000 / 1000163) := by
    rw [show ((1000163 / 1000000) : ℝ) = ((1000000 / 1000163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1780_neg : (163013 / 1000000000) ≤ -Real.log (999837 / 1000000) ∧
    -Real.log (999837 / 1000000) ≤ (81507 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1999837)) (n := 12)
    (lo := (163013 / 1000000000)) (hi := (81507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999837) = 1/(999837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1780 : Bounds (-81507 / 500000000) (-163013 / 1000000000) (Real.log (999837 / 1000000)) := by
  have h := reflection_log_1780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1781_neg : (19647567 / 250000000) ≤ -Real.log (1000000 / 1081761) ∧
    -Real.log (1000000 / 1081761) ≤ (78590269 / 1000000000) := by
  have h := checkLog_sound (w := (81761 / 2081761)) (n := 12)
    (lo := (19647567 / 250000000)) (hi := (78590269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081761 / 1000000) = 1/(1000000 / 1081761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1781 : Bounds (19647567 / 250000000) (78590269 / 1000000000) (Real.log (1081761 / 1000000)) := by
  have h := reflection_log_1781_neg
  have he : Real.log (1081761 / 1000000) = -Real.log (1000000 / 1081761) := by
    rw [show ((1081761 / 1000000) : ℝ) = ((1000000 / 1081761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1782_neg : (85297573 / 1000000000) ≤ -Real.log (918239 / 1000000) ∧
    -Real.log (918239 / 1000000) ≤ (42648787 / 500000000) := by
  have h := checkLog_sound (w := (81761 / 1918239)) (n := 12)
    (lo := (85297573 / 1000000000)) (hi := (42648787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918239) = 1/(918239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1782 : Bounds (-42648787 / 500000000) (-85297573 / 1000000000) (Real.log (918239 / 1000000)) := by
  have h := reflection_log_1782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1783_neg : (39394037 / 500000000) ≤ -Real.log (40000 / 43279) ∧
    -Real.log (40000 / 43279) ≤ (3151523 / 40000000) := by
  have h := checkLog_sound (w := (3279 / 83279)) (n := 12)
    (lo := (39394037 / 500000000)) (hi := (3151523 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43279 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43279 / 40000) = 1/(40000 / 43279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1783 : Bounds (39394037 / 500000000) (3151523 / 40000000) (Real.log (43279 / 40000)) := by
  have h := reflection_log_1783_neg
  have he : Real.log (43279 / 40000) = -Real.log (40000 / 43279) := by
    rw [show ((43279 / 40000) : ℝ) = ((40000 / 43279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1784_neg : (17106131 / 200000000) ≤ -Real.log (36721 / 40000) ∧
    -Real.log (36721 / 40000) ≤ (2672833 / 31250000) := by
  have h := checkLog_sound (w := (3279 / 76721)) (n := 12)
    (lo := (17106131 / 200000000)) (hi := (2672833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36721) = 1/(36721 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1784 : Bounds (-2672833 / 31250000) (-17106131 / 200000000) (Real.log (36721 / 40000)) := by
  have h := reflection_log_1784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1785_neg : (337129 / 50000000) ≤ -Real.log (1589248159 / 1600000000) ∧
    -Real.log (1589248159 / 1600000000) ≤ (6742581 / 1000000000) := by
  have h := checkLog_sound (w := (10751841 / 3189248159)) (n := 12)
    (lo := (337129 / 50000000)) (hi := (6742581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1589248159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1589248159) = 1/(1589248159 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1785 : Bounds (-6742581 / 1000000000) (-337129 / 50000000) (Real.log (1589248159 / 1600000000)) := by
  have h := reflection_log_1785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1786_neg : (838413 / 125000000) ≤ -Real.log (993315138879 / 1000000000000) ∧
    -Real.log (993315138879 / 1000000000000) ≤ (1341461 / 200000000) := by
  have h := checkLog_sound (w := (6684861121 / 1993315138879)) (n := 12)
    (lo := (838413 / 125000000)) (hi := (1341461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993315138879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993315138879) = 1/(993315138879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1786 : Bounds (-1341461 / 200000000) (-838413 / 125000000) (Real.log (993315138879 / 1000000000000)) := by
  have h := reflection_log_1786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1787_neg : (81943921 / 500000000) ≤ -Real.log (500000000000 / 589041088431) ∧
    -Real.log (500000000000 / 589041088431) ≤ (163887843 / 1000000000) := by
  have h := checkLog_sound (w := (89041088431 / 1089041088431)) (n := 12)
    (lo := (81943921 / 500000000)) (hi := (163887843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589041088431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589041088431 / 500000000000) = 1/(500000000000 / 589041088431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1787 : Bounds (81943921 / 500000000) (163887843 / 1000000000) (Real.log (589041088431 / 500000000000)) := by
  have h := reflection_log_1787_neg
  have he : Real.log (589041088431 / 500000000000) = -Real.log (500000000000 / 589041088431) := by
    rw [show ((589041088431 / 500000000000) : ℝ) = ((500000000000 / 589041088431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1788_neg : (16431873 / 100000000) ≤ -Real.log (250000000000 / 294647476921) ∧
    -Real.log (250000000000 / 294647476921) ≤ (164318731 / 1000000000) := by
  have h := checkLog_sound (w := (44647476921 / 544647476921)) (n := 12)
    (lo := (16431873 / 100000000)) (hi := (164318731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294647476921 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294647476921 / 250000000000) = 1/(250000000000 / 294647476921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1788 : Bounds (16431873 / 100000000) (164318731 / 1000000000) (Real.log (294647476921 / 250000000000)) := by
  have h := reflection_log_1788_neg
  have he : Real.log (294647476921 / 250000000000) = -Real.log (250000000000 / 294647476921) := by
    rw [show ((294647476921 / 250000000000) : ℝ) = ((250000000000 / 294647476921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1789_neg : (164364313 / 500000000) ≤ -Real.log (125000000000 / 173650101541) ∧
    -Real.log (125000000000 / 173650101541) ≤ (328728627 / 1000000000) := by
  have h := checkLog_sound (w := (48650101541 / 298650101541)) (n := 12)
    (lo := (164364313 / 500000000)) (hi := (328728627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173650101541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173650101541 / 125000000000) = 1/(125000000000 / 173650101541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1789 : Bounds (164364313 / 500000000) (328728627 / 1000000000) (Real.log (173650101541 / 125000000000)) := by
  have h := reflection_log_1789_neg
  have he : Real.log (173650101541 / 125000000000) = -Real.log (125000000000 / 173650101541) := by
    rw [show ((173650101541 / 125000000000) : ℝ) = ((125000000000 / 173650101541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1790_neg : (164467041 / 500000000) ≤ -Real.log (125000000000 / 173685782557) ∧
    -Real.log (125000000000 / 173685782557) ≤ (328934083 / 1000000000) := by
  have h := checkLog_sound (w := (48685782557 / 298685782557)) (n := 12)
    (lo := (164467041 / 500000000)) (hi := (328934083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173685782557 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173685782557 / 125000000000) = 1/(125000000000 / 173685782557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1790 : Bounds (164467041 / 500000000) (328934083 / 1000000000) (Real.log (173685782557 / 125000000000)) := by
  have h := reflection_log_1790_neg
  have he : Real.log (173685782557 / 125000000000) = -Real.log (125000000000 / 173685782557) := by
    rw [show ((173685782557 / 125000000000) : ℝ) = ((125000000000 / 173685782557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1791_neg : (75544427 / 500000000) ≤ -Real.log (10000 / 11631) ∧
    -Real.log (10000 / 11631) ≤ (30217771 / 200000000) := by
  have h := checkLog_sound (w := (1631 / 21631)) (n := 12)
    (lo := (75544427 / 500000000)) (hi := (30217771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11631 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11631 / 10000) = 1/(10000 / 11631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1791 : Bounds (75544427 / 500000000) (30217771 / 200000000) (Real.log (11631 / 10000)) := by
  have h := reflection_log_1791_neg
  have he : Real.log (11631 / 10000) = -Real.log (10000 / 11631) := by
    rw [show ((11631 / 10000) : ℝ) = ((10000 / 11631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0028 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1792_neg : (178050689 / 1000000000) ≤ -Real.log (8369 / 10000) ∧
    -Real.log (8369 / 10000) ≤ (17805069 / 100000000) := by
  have h := checkLog_sound (w := (1631 / 18369)) (n := 12)
    (lo := (178050689 / 1000000000)) (hi := (17805069 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8369) = 1/(8369 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1792 : Bounds (-17805069 / 100000000) (-178050689 / 1000000000) (Real.log (8369 / 10000)) := by
  have h := reflection_log_1792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1793_neg : (81543 / 500000000) ≤ -Real.log (10000000 / 10001631) ∧
    -Real.log (10000000 / 10001631) ≤ (163087 / 1000000000) := by
  have h := checkLog_sound (w := (1631 / 20001631)) (n := 12)
    (lo := (81543 / 500000000)) (hi := (163087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001631 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001631 / 10000000) = 1/(10000000 / 10001631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1793 : Bounds (81543 / 500000000) (163087 / 1000000000) (Real.log (10001631 / 10000000)) := by
  have h := reflection_log_1793_neg
  have he : Real.log (10001631 / 10000000) = -Real.log (10000000 / 10001631) := by
    rw [show ((10001631 / 10000000) : ℝ) = ((10000000 / 10001631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1794_neg : (163113 / 1000000000) ≤ -Real.log (9998369 / 10000000) ∧
    -Real.log (9998369 / 10000000) ≤ (81557 / 500000000) := by
  have h := checkLog_sound (w := (1631 / 19998369)) (n := 12)
    (lo := (163113 / 1000000000)) (hi := (81557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998369) = 1/(9998369 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1794 : Bounds (-81557 / 500000000) (-163113 / 1000000000) (Real.log (9998369 / 10000000)) := by
  have h := reflection_log_1794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1795_neg : (78637413 / 1000000000) ≤ -Real.log (250000 / 270453) ∧
    -Real.log (250000 / 270453) ≤ (39318707 / 500000000) := by
  have h := checkLog_sound (w := (20453 / 520453)) (n := 12)
    (lo := (78637413 / 1000000000)) (hi := (39318707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270453 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270453 / 250000) = 1/(250000 / 270453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1795 : Bounds (78637413 / 1000000000) (39318707 / 500000000) (Real.log (270453 / 250000)) := by
  have h := reflection_log_1795_neg
  have he : Real.log (270453 / 250000) = -Real.log (250000 / 270453) := by
    rw [show ((270453 / 250000) : ℝ) = ((250000 / 270453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1796_neg : (21338279 / 250000000) ≤ -Real.log (229547 / 250000) ∧
    -Real.log (229547 / 250000) ≤ (85353117 / 1000000000) := by
  have h := checkLog_sound (w := (20453 / 479547)) (n := 12)
    (lo := (21338279 / 250000000)) (hi := (85353117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229547) = 1/(229547 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1796 : Bounds (-85353117 / 1000000000) (-21338279 / 250000000) (Real.log (229547 / 250000)) := by
  have h := reflection_log_1796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1797_neg : (78835209 / 1000000000) ≤ -Real.log (500000 / 541013) ∧
    -Real.log (500000 / 541013) ≤ (7883521 / 100000000) := by
  have h := checkLog_sound (w := (41013 / 1041013)) (n := 12)
    (lo := (78835209 / 1000000000)) (hi := (7883521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541013 / 500000) = 1/(500000 / 541013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1797 : Bounds (78835209 / 1000000000) (7883521 / 100000000) (Real.log (541013 / 500000)) := by
  have h := reflection_log_1797_neg
  have he : Real.log (541013 / 500000) = -Real.log (500000 / 541013) := by
    rw [show ((541013 / 500000) : ℝ) = ((500000 / 541013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1798_neg : (85586211 / 1000000000) ≤ -Real.log (458987 / 500000) ∧
    -Real.log (458987 / 500000) ≤ (21396553 / 250000000) := by
  have h := checkLog_sound (w := (41013 / 958987)) (n := 12)
    (lo := (85586211 / 1000000000)) (hi := (21396553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458987) = 1/(458987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1798 : Bounds (-21396553 / 250000000) (-85586211 / 1000000000) (Real.log (458987 / 500000)) := by
  have h := reflection_log_1798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1799_neg : (6751001 / 1000000000) ≤ -Real.log (248317933831 / 250000000000) ∧
    -Real.log (248317933831 / 250000000000) ≤ (3375501 / 500000000) := by
  have h := checkLog_sound (w := (1682066169 / 498317933831)) (n := 12)
    (lo := (6751001 / 1000000000)) (hi := (3375501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248317933831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248317933831) = 1/(248317933831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1799 : Bounds (-3375501 / 500000000) (-6751001 / 1000000000) (Real.log (248317933831 / 250000000000)) := by
  have h := reflection_log_1799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1800_neg : (6715703 / 1000000000) ≤ -Real.log (62081674791 / 62500000000) ∧
    -Real.log (62081674791 / 62500000000) ≤ (839463 / 125000000) := by
  have h := checkLog_sound (w := (418325209 / 124581674791)) (n := 12)
    (lo := (6715703 / 1000000000)) (hi := (839463 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62081674791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62081674791) = 1/(62081674791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1800 : Bounds (-839463 / 125000000) (-6715703 / 1000000000) (Real.log (62081674791 / 62500000000)) := by
  have h := reflection_log_1800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1801_neg : (163990529 / 1000000000) ≤ -Real.log (250000000000 / 294550789163) ∧
    -Real.log (250000000000 / 294550789163) ≤ (16399053 / 100000000) := by
  have h := checkLog_sound (w := (44550789163 / 544550789163)) (n := 12)
    (lo := (163990529 / 1000000000)) (hi := (16399053 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294550789163 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294550789163 / 250000000000) = 1/(250000000000 / 294550789163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1801 : Bounds (163990529 / 1000000000) (16399053 / 100000000) (Real.log (294550789163 / 250000000000)) := by
  have h := reflection_log_1801_neg
  have he : Real.log (294550789163 / 250000000000) = -Real.log (250000000000 / 294550789163) := by
    rw [show ((294550789163 / 250000000000) : ℝ) = ((250000000000 / 294550789163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1802_neg : (8221071 / 50000000) ≤ -Real.log (250000000000 / 294677735971) ∧
    -Real.log (250000000000 / 294677735971) ≤ (164421421 / 1000000000) := by
  have h := checkLog_sound (w := (44677735971 / 544677735971)) (n := 12)
    (lo := (8221071 / 50000000)) (hi := (164421421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294677735971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294677735971 / 250000000000) = 1/(250000000000 / 294677735971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1802 : Bounds (8221071 / 50000000) (164421421 / 1000000000) (Real.log (294677735971 / 250000000000)) := by
  have h := reflection_log_1802_neg
  have he : Real.log (294677735971 / 250000000000) = -Real.log (250000000000 / 294677735971) := by
    rw [show ((294677735971 / 250000000000) : ℝ) = ((250000000000 / 294677735971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1803_neg : (164467041 / 500000000) ≤ -Real.log (500000000000 / 694743130227) ∧
    -Real.log (500000000000 / 694743130227) ≤ (328934083 / 1000000000) := by
  have h := checkLog_sound (w := (194743130227 / 1194743130227)) (n := 12)
    (lo := (164467041 / 500000000)) (hi := (328934083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694743130227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694743130227 / 500000000000) = 1/(500000000000 / 694743130227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1803 : Bounds (164467041 / 500000000) (328934083 / 1000000000) (Real.log (694743130227 / 500000000000)) := by
  have h := reflection_log_1803_neg
  have he : Real.log (694743130227 / 500000000000) = -Real.log (500000000000 / 694743130227) := by
    rw [show ((694743130227 / 500000000000) : ℝ) = ((500000000000 / 694743130227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1804_neg : (41142443 / 125000000) ≤ -Real.log (250000000000 / 347442944199) ∧
    -Real.log (250000000000 / 347442944199) ≤ (65827909 / 200000000) := by
  have h := checkLog_sound (w := (97442944199 / 597442944199)) (n := 12)
    (lo := (41142443 / 125000000)) (hi := (65827909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347442944199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347442944199 / 250000000000) = 1/(250000000000 / 347442944199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1804 : Bounds (41142443 / 125000000) (65827909 / 200000000) (Real.log (347442944199 / 250000000000)) := by
  have h := reflection_log_1804_neg
  have he : Real.log (347442944199 / 250000000000) = -Real.log (250000000000 / 347442944199) := by
    rw [show ((347442944199 / 250000000000) : ℝ) = ((250000000000 / 347442944199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1805_neg : (151174827 / 1000000000) ≤ -Real.log (625 / 727) ∧
    -Real.log (625 / 727) ≤ (37793707 / 250000000) := by
  have h := checkLog_sound (w := (51 / 676)) (n := 12)
    (lo := (151174827 / 1000000000)) (hi := (37793707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 625) = 1/(625 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1805 : Bounds (151174827 / 1000000000) (37793707 / 250000000) (Real.log (727 / 625)) := by
  have h := reflection_log_1805_neg
  have he : Real.log (727 / 625) = -Real.log (625 / 727) := by
    rw [show ((727 / 625) : ℝ) = ((625 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1806_neg : (35634037 / 200000000) ≤ -Real.log (523 / 625) ∧
    -Real.log (523 / 625) ≤ (89085093 / 500000000) := by
  have h := checkLog_sound (w := (51 / 574)) (n := 12)
    (lo := (35634037 / 200000000)) (hi := (89085093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 523) = 1/(523 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1806 : Bounds (-89085093 / 500000000) (-35634037 / 200000000) (Real.log (523 / 625)) := by
  have h := reflection_log_1806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1807_neg : (81593 / 500000000) ≤ -Real.log (312500 / 312551) ∧
    -Real.log (312500 / 312551) ≤ (163187 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 625051)) (n := 12)
    (lo := (81593 / 500000000)) (hi := (163187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312551 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312551 / 312500) = 1/(312500 / 312551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1807 : Bounds (81593 / 500000000) (163187 / 1000000000) (Real.log (312551 / 312500)) := by
  have h := reflection_log_1807_neg
  have he : Real.log (312551 / 312500) = -Real.log (312500 / 312551) := by
    rw [show ((312551 / 312500) : ℝ) = ((312500 / 312551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1808_neg : (163213 / 1000000000) ≤ -Real.log (312449 / 312500) ∧
    -Real.log (312449 / 312500) ≤ (81607 / 500000000) := by
  have h := checkLog_sound (w := (51 / 624949)) (n := 12)
    (lo := (163213 / 1000000000)) (hi := (81607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312449) = 1/(312449 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1808 : Bounds (-81607 / 500000000) (-163213 / 1000000000) (Real.log (312449 / 312500)) := by
  have h := reflection_log_1808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1809_neg : (15736911 / 200000000) ≤ -Real.log (1000000 / 1081863) ∧
    -Real.log (1000000 / 1081863) ≤ (19671139 / 250000000) := by
  have h := checkLog_sound (w := (81863 / 2081863)) (n := 12)
    (lo := (15736911 / 200000000)) (hi := (19671139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081863 / 1000000) = 1/(1000000 / 1081863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1809 : Bounds (15736911 / 200000000) (19671139 / 250000000) (Real.log (1081863 / 1000000)) := by
  have h := reflection_log_1809_neg
  have he : Real.log (1081863 / 1000000) = -Real.log (1000000 / 1081863) := by
    rw [show ((1081863 / 1000000) : ℝ) = ((1000000 / 1081863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1810_neg : (42704331 / 500000000) ≤ -Real.log (918137 / 1000000) ∧
    -Real.log (918137 / 1000000) ≤ (85408663 / 1000000000) := by
  have h := checkLog_sound (w := (81863 / 1918137)) (n := 12)
    (lo := (42704331 / 500000000)) (hi := (85408663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918137) = 1/(918137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1810 : Bounds (-85408663 / 1000000000) (-42704331 / 500000000) (Real.log (918137 / 1000000)) := by
  have h := reflection_log_1810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1811_neg : (39441171 / 500000000) ≤ -Real.log (1000000 / 1082077) ∧
    -Real.log (1000000 / 1082077) ≤ (78882343 / 1000000000) := by
  have h := checkLog_sound (w := (82077 / 2082077)) (n := 12)
    (lo := (39441171 / 500000000)) (hi := (78882343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082077 / 1000000) = 1/(1000000 / 1082077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1811 : Bounds (39441171 / 500000000) (78882343 / 1000000000) (Real.log (1082077 / 1000000)) := by
  have h := reflection_log_1811_neg
  have he : Real.log (1082077 / 1000000) = -Real.log (1000000 / 1082077) := by
    rw [show ((1082077 / 1000000) : ℝ) = ((1000000 / 1082077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1812_neg : (85641769 / 1000000000) ≤ -Real.log (917923 / 1000000) ∧
    -Real.log (917923 / 1000000) ≤ (8564177 / 100000000) := by
  have h := checkLog_sound (w := (82077 / 1917923)) (n := 12)
    (lo := (85641769 / 1000000000)) (hi := (8564177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917923) = 1/(917923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1812 : Bounds (-8564177 / 100000000) (-85641769 / 1000000000) (Real.log (917923 / 1000000)) := by
  have h := reflection_log_1812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1813_neg : (6759427 / 1000000000) ≤ -Real.log (993263366071 / 1000000000000) ∧
    -Real.log (993263366071 / 1000000000000) ≤ (1689857 / 250000000) := by
  have h := checkLog_sound (w := (6736633929 / 1993263366071)) (n := 12)
    (lo := (6759427 / 1000000000)) (hi := (1689857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993263366071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993263366071) = 1/(993263366071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1813 : Bounds (-1689857 / 250000000) (-6759427 / 1000000000) (Real.log (993263366071 / 1000000000000)) := by
  have h := reflection_log_1813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1814_neg : (3362053 / 500000000) ≤ -Real.log (993298449231 / 1000000000000) ∧
    -Real.log (993298449231 / 1000000000000) ≤ (6724107 / 1000000000) := by
  have h := checkLog_sound (w := (6701550769 / 1993298449231)) (n := 12)
    (lo := (3362053 / 500000000)) (hi := (6724107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993298449231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993298449231) = 1/(993298449231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1814 : Bounds (-6724107 / 1000000000) (-3362053 / 500000000) (Real.log (993298449231 / 1000000000000)) := by
  have h := reflection_log_1814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1815_neg : (164093217 / 1000000000) ≤ -Real.log (25000000000 / 29458103747) ∧
    -Real.log (25000000000 / 29458103747) ≤ (82046609 / 500000000) := by
  have h := checkLog_sound (w := (4458103747 / 54458103747)) (n := 12)
    (lo := (164093217 / 1000000000)) (hi := (82046609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29458103747 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29458103747 / 25000000000) = 1/(25000000000 / 29458103747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1815 : Bounds (164093217 / 1000000000) (82046609 / 500000000) (Real.log (29458103747 / 25000000000)) := by
  have h := reflection_log_1815_neg
  have he : Real.log (29458103747 / 25000000000) = -Real.log (25000000000 / 29458103747) := by
    rw [show ((29458103747 / 25000000000) : ℝ) = ((25000000000 / 29458103747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1816_neg : (10282757 / 62500000) ≤ -Real.log (500000000000 / 589415996767) ∧
    -Real.log (500000000000 / 589415996767) ≤ (164524113 / 1000000000) := by
  have h := checkLog_sound (w := (89415996767 / 1089415996767)) (n := 12)
    (lo := (10282757 / 62500000)) (hi := (164524113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589415996767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589415996767 / 500000000000) = 1/(500000000000 / 589415996767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1816 : Bounds (10282757 / 62500000) (164524113 / 1000000000) (Real.log (589415996767 / 500000000000)) := by
  have h := reflection_log_1816_neg
  have he : Real.log (589415996767 / 500000000000) = -Real.log (500000000000 / 589415996767) := by
    rw [show ((589415996767 / 500000000000) : ℝ) = ((500000000000 / 589415996767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1817_neg : (41142443 / 125000000) ≤ -Real.log (500000000000 / 694885888397) ∧
    -Real.log (500000000000 / 694885888397) ≤ (65827909 / 200000000) := by
  have h := checkLog_sound (w := (194885888397 / 1194885888397)) (n := 12)
    (lo := (41142443 / 125000000)) (hi := (65827909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694885888397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694885888397 / 500000000000) = 1/(500000000000 / 694885888397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1817 : Bounds (41142443 / 125000000) (65827909 / 200000000) (Real.log (694885888397 / 500000000000)) := by
  have h := reflection_log_1817_neg
  have he : Real.log (694885888397 / 500000000000) = -Real.log (500000000000 / 694885888397) := by
    rw [show ((694885888397 / 500000000000) : ℝ) = ((500000000000 / 694885888397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1818_neg : (329345013 / 1000000000) ≤ -Real.log (500000000000 / 695028680689) ∧
    -Real.log (500000000000 / 695028680689) ≤ (164672507 / 500000000) := by
  have h := checkLog_sound (w := (195028680689 / 1195028680689)) (n := 12)
    (lo := (329345013 / 1000000000)) (hi := (164672507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695028680689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695028680689 / 500000000000) = 1/(500000000000 / 695028680689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1818 : Bounds (329345013 / 1000000000) (164672507 / 500000000) (Real.log (695028680689 / 500000000000)) := by
  have h := reflection_log_1818_neg
  have he : Real.log (695028680689 / 500000000000) = -Real.log (500000000000 / 695028680689) := by
    rw [show ((695028680689 / 500000000000) : ℝ) = ((500000000000 / 695028680689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1819_neg : (151260793 / 1000000000) ≤ -Real.log (10000 / 11633) ∧
    -Real.log (10000 / 11633) ≤ (75630397 / 500000000) := by
  have h := checkLog_sound (w := (1633 / 21633)) (n := 12)
    (lo := (151260793 / 1000000000)) (hi := (75630397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11633 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11633 / 10000) = 1/(10000 / 11633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1819 : Bounds (151260793 / 1000000000) (75630397 / 500000000) (Real.log (11633 / 10000)) := by
  have h := reflection_log_1819_neg
  have he : Real.log (11633 / 10000) = -Real.log (10000 / 11633) := by
    rw [show ((11633 / 10000) : ℝ) = ((10000 / 11633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1820_neg : (35657939 / 200000000) ≤ -Real.log (8367 / 10000) ∧
    -Real.log (8367 / 10000) ≤ (5571553 / 31250000) := by
  have h := checkLog_sound (w := (1633 / 18367)) (n := 12)
    (lo := (35657939 / 200000000)) (hi := (5571553 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8367) = 1/(8367 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1820 : Bounds (-5571553 / 31250000) (-35657939 / 200000000) (Real.log (8367 / 10000)) := by
  have h := reflection_log_1820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1821_neg : (81643 / 500000000) ≤ -Real.log (10000000 / 10001633) ∧
    -Real.log (10000000 / 10001633) ≤ (163287 / 1000000000) := by
  have h := checkLog_sound (w := (1633 / 20001633)) (n := 12)
    (lo := (81643 / 500000000)) (hi := (163287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001633 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001633 / 10000000) = 1/(10000000 / 10001633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1821 : Bounds (81643 / 500000000) (163287 / 1000000000) (Real.log (10001633 / 10000000)) := by
  have h := reflection_log_1821_neg
  have he : Real.log (10001633 / 10000000) = -Real.log (10000000 / 10001633) := by
    rw [show ((10001633 / 10000000) : ℝ) = ((10000000 / 10001633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1822_neg : (163313 / 1000000000) ≤ -Real.log (9998367 / 10000000) ∧
    -Real.log (9998367 / 10000000) ≤ (81657 / 500000000) := by
  have h := checkLog_sound (w := (1633 / 19998367)) (n := 12)
    (lo := (163313 / 1000000000)) (hi := (81657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998367) = 1/(9998367 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1822 : Bounds (-81657 / 500000000) (-163313 / 1000000000) (Real.log (9998367 / 10000000)) := by
  have h := reflection_log_1822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1823_neg : (7873077 / 100000000) ≤ -Real.log (1000000 / 1081913) ∧
    -Real.log (1000000 / 1081913) ≤ (78730771 / 1000000000) := by
  have h := checkLog_sound (w := (81913 / 2081913)) (n := 12)
    (lo := (7873077 / 100000000)) (hi := (78730771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081913 / 1000000) = 1/(1000000 / 1081913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1823 : Bounds (7873077 / 100000000) (78730771 / 1000000000) (Real.log (1081913 / 1000000)) := by
  have h := reflection_log_1823_neg
  have he : Real.log (1081913 / 1000000) = -Real.log (1000000 / 1081913) := by
    rw [show ((1081913 / 1000000) : ℝ) = ((1000000 / 1081913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1824_neg : (85463121 / 1000000000) ≤ -Real.log (918087 / 1000000) ∧
    -Real.log (918087 / 1000000) ≤ (42731561 / 500000000) := by
  have h := checkLog_sound (w := (81913 / 1918087)) (n := 12)
    (lo := (85463121 / 1000000000)) (hi := (42731561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918087) = 1/(918087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1824 : Bounds (-42731561 / 500000000) (-85463121 / 1000000000) (Real.log (918087 / 1000000)) := by
  have h := reflection_log_1824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1825_neg : (1233273 / 15625000) ≤ -Real.log (62500 / 67633) ∧
    -Real.log (62500 / 67633) ≤ (78929473 / 1000000000) := by
  have h := checkLog_sound (w := (5133 / 130133)) (n := 12)
    (lo := (1233273 / 15625000)) (hi := (78929473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67633 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67633 / 62500) = 1/(62500 / 67633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1825 : Bounds (1233273 / 15625000) (78929473 / 1000000000) (Real.log (67633 / 62500)) := by
  have h := reflection_log_1825_neg
  have he : Real.log (67633 / 62500) = -Real.log (62500 / 67633) := by
    rw [show ((67633 / 62500) : ℝ) = ((62500 / 67633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1826_neg : (85697331 / 1000000000) ≤ -Real.log (57367 / 62500) ∧
    -Real.log (57367 / 62500) ≤ (21424333 / 250000000) := by
  have h := checkLog_sound (w := (5133 / 119867)) (n := 12)
    (lo := (85697331 / 1000000000)) (hi := (21424333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57367) = 1/(57367 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1826 : Bounds (-21424333 / 250000000) (-85697331 / 1000000000) (Real.log (57367 / 62500)) := by
  have h := reflection_log_1826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1827_neg : (3383929 / 500000000) ≤ -Real.log (3879902311 / 3906250000) ∧
    -Real.log (3879902311 / 3906250000) ≤ (6767859 / 1000000000) := by
  have h := checkLog_sound (w := (26347689 / 7786152311)) (n := 12)
    (lo := (3383929 / 500000000)) (hi := (6767859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3879902311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3879902311) = 1/(3879902311 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1827 : Bounds (-6767859 / 1000000000) (-3383929 / 500000000) (Real.log (3879902311 / 3906250000)) := by
  have h := reflection_log_1827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1828_neg : (6732351 / 1000000000) ≤ -Real.log (993290260431 / 1000000000000) ∧
    -Real.log (993290260431 / 1000000000000) ≤ (105193 / 15625000) := by
  have h := checkLog_sound (w := (6709739569 / 1993290260431)) (n := 12)
    (lo := (6732351 / 1000000000)) (hi := (105193 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993290260431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993290260431) = 1/(993290260431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1828 : Bounds (-105193 / 15625000) (-6732351 / 1000000000) (Real.log (993290260431 / 1000000000000)) := by
  have h := reflection_log_1828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1829_neg : (41048473 / 250000000) ≤ -Real.log (976562500 / 1150823031) ∧
    -Real.log (976562500 / 1150823031) ≤ (164193893 / 1000000000) := by
  have h := checkLog_sound (w := (174260531 / 2127385531)) (n := 12)
    (lo := (41048473 / 250000000)) (hi := (164193893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150823031 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150823031 / 976562500) = 1/(976562500 / 1150823031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1829 : Bounds (41048473 / 250000000) (164193893 / 1000000000) (Real.log (1150823031 / 976562500)) := by
  have h := reflection_log_1829_neg
  have he : Real.log (1150823031 / 976562500) = -Real.log (976562500 / 1150823031) := by
    rw [show ((1150823031 / 976562500) : ℝ) = ((976562500 / 1150823031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1830_neg : (41156701 / 250000000) ≤ -Real.log (250000000000 / 294738264159) ∧
    -Real.log (250000000000 / 294738264159) ≤ (32925361 / 200000000) := by
  have h := checkLog_sound (w := (44738264159 / 544738264159)) (n := 12)
    (lo := (41156701 / 250000000)) (hi := (32925361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294738264159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294738264159 / 250000000000) = 1/(250000000000 / 294738264159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1830 : Bounds (41156701 / 250000000) (32925361 / 200000000) (Real.log (294738264159 / 250000000000)) := by
  have h := reflection_log_1830_neg
  have he : Real.log (294738264159 / 250000000000) = -Real.log (250000000000 / 294738264159) := by
    rw [show ((294738264159 / 250000000000) : ℝ) = ((250000000000 / 294738264159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1831_neg : (329345013 / 1000000000) ≤ -Real.log (31250000000 / 43439292543) ∧
    -Real.log (31250000000 / 43439292543) ≤ (164672507 / 500000000) := by
  have h := checkLog_sound (w := (12189292543 / 74689292543)) (n := 12)
    (lo := (329345013 / 1000000000)) (hi := (164672507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43439292543 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43439292543 / 31250000000) = 1/(31250000000 / 43439292543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1831 : Bounds (329345013 / 1000000000) (164672507 / 500000000) (Real.log (43439292543 / 31250000000)) := by
  have h := reflection_log_1831_neg
  have he : Real.log (43439292543 / 31250000000) = -Real.log (31250000000 / 43439292543) := by
    rw [show ((43439292543 / 31250000000) : ℝ) = ((31250000000 / 43439292543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1832_neg : (329550489 / 1000000000) ≤ -Real.log (62500000000 / 86896438389) ∧
    -Real.log (62500000000 / 86896438389) ≤ (32955049 / 100000000) := by
  have h := checkLog_sound (w := (24396438389 / 149396438389)) (n := 12)
    (lo := (329550489 / 1000000000)) (hi := (32955049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86896438389 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86896438389 / 62500000000) = 1/(62500000000 / 86896438389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1832 : Bounds (329550489 / 1000000000) (32955049 / 100000000) (Real.log (86896438389 / 62500000000)) := by
  have h := reflection_log_1832_neg
  have he : Real.log (86896438389 / 62500000000) = -Real.log (62500000000 / 86896438389) := by
    rw [show ((86896438389 / 62500000000) : ℝ) = ((62500000000 / 86896438389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1833_neg : (2364793 / 15625000) ≤ -Real.log (5000 / 5817) ∧
    -Real.log (5000 / 5817) ≤ (151346753 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 10817)) (n := 12)
    (lo := (2364793 / 15625000)) (hi := (151346753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5817 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5817 / 5000) = 1/(5000 / 5817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1833 : Bounds (2364793 / 15625000) (151346753 / 1000000000) (Real.log (5817 / 5000)) := by
  have h := reflection_log_1833_neg
  have he : Real.log (5817 / 5000) = -Real.log (5000 / 5817) := by
    rw [show ((5817 / 5000) : ℝ) = ((5000 / 5817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1834_neg : (178409219 / 1000000000) ≤ -Real.log (4183 / 5000) ∧
    -Real.log (4183 / 5000) ≤ (8920461 / 50000000) := by
  have h := checkLog_sound (w := (817 / 9183)) (n := 12)
    (lo := (178409219 / 1000000000)) (hi := (8920461 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4183) = 1/(4183 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1834 : Bounds (-8920461 / 50000000) (-178409219 / 1000000000) (Real.log (4183 / 5000)) := by
  have h := reflection_log_1834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1835_neg : (81693 / 500000000) ≤ -Real.log (5000000 / 5000817) ∧
    -Real.log (5000000 / 5000817) ≤ (163387 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 10000817)) (n := 12)
    (lo := (81693 / 500000000)) (hi := (163387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000817 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000817 / 5000000) = 1/(5000000 / 5000817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1835 : Bounds (81693 / 500000000) (163387 / 1000000000) (Real.log (5000817 / 5000000)) := by
  have h := reflection_log_1835_neg
  have he : Real.log (5000817 / 5000000) = -Real.log (5000000 / 5000817) := by
    rw [show ((5000817 / 5000000) : ℝ) = ((5000000 / 5000817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1836_neg : (163413 / 1000000000) ≤ -Real.log (4999183 / 5000000) ∧
    -Real.log (4999183 / 5000000) ≤ (81707 / 500000000) := by
  have h := checkLog_sound (w := (817 / 9999183)) (n := 12)
    (lo := (163413 / 1000000000)) (hi := (81707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999183) = 1/(4999183 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1836 : Bounds (-81707 / 500000000) (-163413 / 1000000000) (Real.log (4999183 / 5000000)) := by
  have h := reflection_log_1836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1837_neg : (19694477 / 250000000) ≤ -Real.log (250000 / 270491) ∧
    -Real.log (250000 / 270491) ≤ (78777909 / 1000000000) := by
  have h := checkLog_sound (w := (20491 / 520491)) (n := 12)
    (lo := (19694477 / 250000000)) (hi := (78777909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270491 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270491 / 250000) = 1/(250000 / 270491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1837 : Bounds (19694477 / 250000000) (78777909 / 1000000000) (Real.log (270491 / 250000)) := by
  have h := reflection_log_1837_neg
  have he : Real.log (270491 / 250000) = -Real.log (250000 / 270491) := by
    rw [show ((270491 / 250000) : ℝ) = ((250000 / 270491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1838_neg : (85518673 / 1000000000) ≤ -Real.log (229509 / 250000) ∧
    -Real.log (229509 / 250000) ≤ (42759337 / 500000000) := by
  have h := checkLog_sound (w := (20491 / 479509)) (n := 12)
    (lo := (85518673 / 1000000000)) (hi := (42759337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229509) = 1/(229509 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1838 : Bounds (-42759337 / 500000000) (-85518673 / 1000000000) (Real.log (229509 / 250000)) := by
  have h := reflection_log_1838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1839_neg : (78975677 / 1000000000) ≤ -Real.log (500000 / 541089) ∧
    -Real.log (500000 / 541089) ≤ (39487839 / 500000000) := by
  have h := checkLog_sound (w := (41089 / 1041089)) (n := 12)
    (lo := (78975677 / 1000000000)) (hi := (39487839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541089 / 500000) = 1/(500000 / 541089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1839 : Bounds (78975677 / 1000000000) (39487839 / 500000000) (Real.log (541089 / 500000)) := by
  have h := reflection_log_1839_neg
  have he : Real.log (541089 / 500000) = -Real.log (500000 / 541089) := by
    rw [show ((541089 / 500000) : ℝ) = ((500000 / 541089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1840_neg : (42875903 / 500000000) ≤ -Real.log (458911 / 500000) ∧
    -Real.log (458911 / 500000) ≤ (85751807 / 1000000000) := by
  have h := checkLog_sound (w := (41089 / 958911)) (n := 12)
    (lo := (42875903 / 500000000)) (hi := (85751807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458911) = 1/(458911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1840 : Bounds (-85751807 / 1000000000) (-42875903 / 500000000) (Real.log (458911 / 500000)) := by
  have h := reflection_log_1840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1841_neg : (6776129 / 1000000000) ≤ -Real.log (248311694079 / 250000000000) ∧
    -Real.log (248311694079 / 250000000000) ≤ (677613 / 100000000) := by
  have h := checkLog_sound (w := (1688305921 / 498311694079)) (n := 12)
    (lo := (6776129 / 1000000000)) (hi := (677613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248311694079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248311694079) = 1/(248311694079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1841 : Bounds (-677613 / 100000000) (-6776129 / 1000000000) (Real.log (248311694079 / 250000000000)) := by
  have h := reflection_log_1841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1842_neg : (1348153 / 200000000) ≤ -Real.log (62080118919 / 62500000000) ∧
    -Real.log (62080118919 / 62500000000) ≤ (3370383 / 500000000) := by
  have h := checkLog_sound (w := (419881081 / 124580118919)) (n := 12)
    (lo := (1348153 / 200000000)) (hi := (3370383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62080118919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62080118919) = 1/(62080118919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1842 : Bounds (-3370383 / 500000000) (-1348153 / 200000000) (Real.log (62080118919 / 62500000000)) := by
  have h := reflection_log_1842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1843_neg : (164296581 / 1000000000) ≤ -Real.log (500000000000 / 589281901799) ∧
    -Real.log (500000000000 / 589281901799) ≤ (82148291 / 500000000) := by
  have h := checkLog_sound (w := (89281901799 / 1089281901799)) (n := 12)
    (lo := (164296581 / 1000000000)) (hi := (82148291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589281901799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589281901799 / 500000000000) = 1/(500000000000 / 589281901799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1843 : Bounds (164296581 / 1000000000) (82148291 / 500000000) (Real.log (589281901799 / 500000000000)) := by
  have h := reflection_log_1843_neg
  have he : Real.log (589281901799 / 500000000000) = -Real.log (500000000000 / 589281901799) := by
    rw [show ((589281901799 / 500000000000) : ℝ) = ((500000000000 / 589281901799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1844_neg : (41181871 / 250000000) ≤ -Real.log (500000000000 / 589535879507) ∧
    -Real.log (500000000000 / 589535879507) ≤ (32945497 / 200000000) := by
  have h := checkLog_sound (w := (89535879507 / 1089535879507)) (n := 12)
    (lo := (41181871 / 250000000)) (hi := (32945497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589535879507 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589535879507 / 500000000000) = 1/(500000000000 / 589535879507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1844 : Bounds (41181871 / 250000000) (32945497 / 200000000) (Real.log (589535879507 / 500000000000)) := by
  have h := reflection_log_1844_neg
  have he : Real.log (589535879507 / 500000000000) = -Real.log (500000000000 / 589535879507) := by
    rw [show ((589535879507 / 500000000000) : ℝ) = ((500000000000 / 589535879507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1845_neg : (329550489 / 1000000000) ≤ -Real.log (500000000000 / 695171507111) ∧
    -Real.log (500000000000 / 695171507111) ≤ (32955049 / 100000000) := by
  have h := checkLog_sound (w := (195171507111 / 1195171507111)) (n := 12)
    (lo := (329550489 / 1000000000)) (hi := (32955049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695171507111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695171507111 / 500000000000) = 1/(500000000000 / 695171507111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1845 : Bounds (329550489 / 1000000000) (32955049 / 100000000) (Real.log (695171507111 / 500000000000)) := by
  have h := reflection_log_1845_neg
  have he : Real.log (695171507111 / 500000000000) = -Real.log (500000000000 / 695171507111) := by
    rw [show ((695171507111 / 500000000000) : ℝ) = ((500000000000 / 695171507111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1846_neg : (82438993 / 250000000) ≤ -Real.log (500000000000 / 695314367679) ∧
    -Real.log (500000000000 / 695314367679) ≤ (329755973 / 1000000000) := by
  have h := checkLog_sound (w := (195314367679 / 1195314367679)) (n := 12)
    (lo := (82438993 / 250000000)) (hi := (329755973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695314367679 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695314367679 / 500000000000) = 1/(500000000000 / 695314367679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1846 : Bounds (82438993 / 250000000) (329755973 / 1000000000) (Real.log (695314367679 / 500000000000)) := by
  have h := reflection_log_1846_neg
  have he : Real.log (695314367679 / 500000000000) = -Real.log (500000000000 / 695314367679) := by
    rw [show ((695314367679 / 500000000000) : ℝ) = ((500000000000 / 695314367679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1847_neg : (151432703 / 1000000000) ≤ -Real.log (2000 / 2327) ∧
    -Real.log (2000 / 2327) ≤ (295767 / 1953125) := by
  have h := checkLog_sound (w := (327 / 4327)) (n := 12)
    (lo := (151432703 / 1000000000)) (hi := (295767 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2327 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2327 / 2000) = 1/(2000 / 2327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1847 : Bounds (151432703 / 1000000000) (295767 / 1953125) (Real.log (2327 / 2000)) := by
  have h := reflection_log_1847_neg
  have he : Real.log (2327 / 2000) = -Real.log (2000 / 2327) := by
    rw [show ((2327 / 2000) : ℝ) = ((2000 / 2327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1848_neg : (89264379 / 500000000) ≤ -Real.log (1673 / 2000) ∧
    -Real.log (1673 / 2000) ≤ (178528759 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 3673)) (n := 12)
    (lo := (89264379 / 500000000)) (hi := (178528759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1673) = 1/(1673 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1848 : Bounds (-178528759 / 1000000000) (-89264379 / 500000000) (Real.log (1673 / 2000)) := by
  have h := reflection_log_1848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1849_neg : (81743 / 500000000) ≤ -Real.log (2000000 / 2000327) ∧
    -Real.log (2000000 / 2000327) ≤ (163487 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 4000327)) (n := 12)
    (lo := (81743 / 500000000)) (hi := (163487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000327 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000327 / 2000000) = 1/(2000000 / 2000327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1849 : Bounds (81743 / 500000000) (163487 / 1000000000) (Real.log (2000327 / 2000000)) := by
  have h := reflection_log_1849_neg
  have he : Real.log (2000327 / 2000000) = -Real.log (2000000 / 2000327) := by
    rw [show ((2000327 / 2000000) : ℝ) = ((2000000 / 2000327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1850_neg : (163513 / 1000000000) ≤ -Real.log (1999673 / 2000000) ∧
    -Real.log (1999673 / 2000000) ≤ (81757 / 500000000) := by
  have h := checkLog_sound (w := (327 / 3999673)) (n := 12)
    (lo := (163513 / 1000000000)) (hi := (81757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999673) = 1/(1999673 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1850 : Bounds (-81757 / 500000000) (-163513 / 1000000000) (Real.log (1999673 / 2000000)) := by
  have h := reflection_log_1850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1851_neg : (78825043 / 1000000000) ≤ -Real.log (200000 / 216403) ∧
    -Real.log (200000 / 216403) ≤ (19706261 / 250000000) := by
  have h := checkLog_sound (w := (16403 / 416403)) (n := 12)
    (lo := (78825043 / 1000000000)) (hi := (19706261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216403 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216403 / 200000) = 1/(200000 / 216403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1851 : Bounds (78825043 / 1000000000) (19706261 / 250000000) (Real.log (216403 / 200000)) := by
  have h := reflection_log_1851_neg
  have he : Real.log (216403 / 200000) = -Real.log (200000 / 216403) := by
    rw [show ((216403 / 200000) : ℝ) = ((200000 / 216403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1852_neg : (21393557 / 250000000) ≤ -Real.log (183597 / 200000) ∧
    -Real.log (183597 / 200000) ≤ (85574229 / 1000000000) := by
  have h := checkLog_sound (w := (16403 / 383597)) (n := 12)
    (lo := (21393557 / 250000000)) (hi := (85574229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183597) = 1/(183597 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1852 : Bounds (-85574229 / 1000000000) (-21393557 / 250000000) (Real.log (183597 / 200000)) := by
  have h := reflection_log_1852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1853_neg : (79022803 / 1000000000) ≤ -Real.log (1000000 / 1082229) ∧
    -Real.log (1000000 / 1082229) ≤ (19755701 / 250000000) := by
  have h := checkLog_sound (w := (82229 / 2082229)) (n := 12)
    (lo := (79022803 / 1000000000)) (hi := (19755701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082229 / 1000000) = 1/(1000000 / 1082229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1853 : Bounds (79022803 / 1000000000) (19755701 / 250000000) (Real.log (1082229 / 1000000)) := by
  have h := reflection_log_1853_neg
  have he : Real.log (1082229 / 1000000) = -Real.log (1000000 / 1082229) := by
    rw [show ((1082229 / 1000000) : ℝ) = ((1000000 / 1082229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1854_neg : (42903687 / 500000000) ≤ -Real.log (917771 / 1000000) ∧
    -Real.log (917771 / 1000000) ≤ (686459 / 8000000) := by
  have h := checkLog_sound (w := (82229 / 1917771)) (n := 12)
    (lo := (42903687 / 500000000)) (hi := (686459 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917771) = 1/(917771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1854 : Bounds (-686459 / 8000000) (-42903687 / 500000000) (Real.log (917771 / 1000000)) := by
  have h := reflection_log_1854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1855_neg : (6784571 / 1000000000) ≤ -Real.log (993238391559 / 1000000000000) ∧
    -Real.log (993238391559 / 1000000000000) ≤ (1696143 / 250000000) := by
  have h := checkLog_sound (w := (6761608441 / 1993238391559)) (n := 12)
    (lo := (6784571 / 1000000000)) (hi := (1696143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993238391559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993238391559) = 1/(993238391559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1855 : Bounds (-1696143 / 250000000) (-6784571 / 1000000000) (Real.log (993238391559 / 1000000000000)) := by
  have h := reflection_log_1855_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


