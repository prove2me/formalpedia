-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0229__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0229__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T04:09:18.500335+00:00
-- url     : https://prove2.me/theorems/23f4bb50-b965-4c8e-9324-ac188a9b497f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0229 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0230, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0229 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0230, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0231)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0229 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0230, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0231)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0229 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0230, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0231) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0229 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0230, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0231).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0229 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14656_neg : (432210237 / 1000000000) ≤ -Real.log (649072903119 / 1000000000000) ∧
    -Real.log (649072903119 / 1000000000000) ≤ (216105119 / 500000000) := by
  have h := checkLog_sound (w := (350927096881 / 1649072903119)) (n := 12)
    (lo := (432210237 / 1000000000)) (hi := (216105119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 649072903119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 649072903119) = 1/(649072903119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14656 : Bounds (-216105119 / 500000000) (-432210237 / 1000000000) (Real.log (649072903119 / 1000000000000)) := by
  have h := reflection_log_14656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14657_neg : (1362683557 / 1000000000) ≤ -Real.log (62500000000 / 244166437689) ∧
    -Real.log (62500000000 / 244166437689) ≤ (1362683559 / 1000000000) := by
  have h := checkLog_sound (w := (119166437689 / 369166437689)) (n := 12)
    (lo := (669536377 / 1000000000)) (hi := (334768189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244166437689 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(244166437689 / 125000000000) = 1/(62500000000 / 244166437689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14657 : Bounds (1362683557 / 1000000000) (1362683559 / 1000000000) (Real.log (244166437689 / 62500000000)) := by
  have h := reflection_log_14657_neg
  have he : Real.log (244166437689 / 62500000000) = -Real.log (62500000000 / 244166437689) := by
    rw [show ((244166437689 / 62500000000) : ℝ) = ((62500000000 / 244166437689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14658_neg : (1368096867 / 1000000000) ≤ -Real.log (3125000000 / 12274588523) ∧
    -Real.log (3125000000 / 12274588523) ≤ (1368096869 / 1000000000) := by
  have h := checkLog_sound (w := (6024588523 / 18524588523)) (n := 12)
    (lo := (674949687 / 1000000000)) (hi := (84368711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12274588523 / 6250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12274588523 / 6250000000) = 1/(3125000000 / 12274588523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14658 : Bounds (1368096867 / 1000000000) (1368096869 / 1000000000) (Real.log (12274588523 / 3125000000)) := by
  have h := reflection_log_14658_neg
  have he : Real.log (12274588523 / 3125000000) = -Real.log (3125000000 / 12274588523) := by
    rw [show ((12274588523 / 3125000000) : ℝ) = ((3125000000 / 12274588523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14659_neg : (3684277039 / 1000000000) ≤ -Real.log (500000000000 / 19908163265307) ∧
    -Real.log (500000000000 / 19908163265307) ≤ (736855409 / 200000000) := by
  have h := checkLog_sound (w := (3908163265307 / 35908163265307)) (n := 12)
    (lo := (218541139 / 1000000000)) (hi := (10927057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19908163265307 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19908163265307 / 16000000000000) = 1/(500000000000 / 19908163265307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14659 : Bounds (3684277039 / 1000000000) (736855409 / 200000000) (Real.log (19908163265307 / 500000000000)) := by
  have h := reflection_log_14659_neg
  have he : Real.log (19908163265307 / 500000000000) = -Real.log (500000000000 / 19908163265307) := by
    rw [show ((19908163265307 / 500000000000) : ℝ) = ((500000000000 / 19908163265307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14660_neg : (668854487 / 1000000000) ≤ -Real.log (125 / 244) ∧
    -Real.log (125 / 244) ≤ (83606811 / 125000000) := by
  have h := checkLog_sound (w := (119 / 369)) (n := 12)
    (lo := (668854487 / 1000000000)) (hi := (83606811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244 / 125) = 1/(125 / 244) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14660 : Bounds (668854487 / 1000000000) (83606811 / 125000000) (Real.log (244 / 125)) := by
  have h := reflection_log_14660_neg
  have he : Real.log (244 / 125) = -Real.log (125 / 244) := by
    rw [show ((244 / 125) : ℝ) = ((125 / 244) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14661_neg : (607310853 / 200000000) ≤ -Real.log (6 / 125) ∧
    -Real.log (6 / 125) ≤ (303655427 / 100000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 96) = 1/(6 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14661 : Bounds (-303655427 / 100000000) (-607310853 / 200000000) (Real.log (6 / 125)) := by
  have h := reflection_log_14661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14662_neg : (951547 / 1000000000) ≤ -Real.log (125000 / 125119) ∧
    -Real.log (125000 / 125119) ≤ (237887 / 250000000) := by
  have h := checkLog_sound (w := (119 / 250119)) (n := 12)
    (lo := (951547 / 1000000000)) (hi := (237887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125119 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125119 / 125000) = 1/(125000 / 125119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14662 : Bounds (951547 / 1000000000) (237887 / 250000000) (Real.log (125119 / 125000)) := by
  have h := reflection_log_14662_neg
  have he : Real.log (125119 / 125000) = -Real.log (125000 / 125119) := by
    rw [show ((125119 / 125000) : ℝ) = ((125000 / 125119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14663_neg : (952453 / 1000000000) ≤ -Real.log (124881 / 125000) ∧
    -Real.log (124881 / 125000) ≤ (476227 / 500000000) := by
  have h := checkLog_sound (w := (119 / 249881)) (n := 12)
    (lo := (952453 / 1000000000)) (hi := (476227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124881) = 1/(124881 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14663 : Bounds (-476227 / 500000000) (-952453 / 1000000000) (Real.log (124881 / 125000)) := by
  have h := reflection_log_14663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14664_neg : (465923441 / 1000000000) ≤ -Real.log (200000 / 318697) ∧
    -Real.log (200000 / 318697) ≤ (232961721 / 500000000) := by
  have h := checkLog_sound (w := (118697 / 518697)) (n := 12)
    (lo := (465923441 / 1000000000)) (hi := (232961721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318697 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318697 / 200000) = 1/(200000 / 318697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14664 : Bounds (465923441 / 1000000000) (232961721 / 500000000) (Real.log (318697 / 200000)) := by
  have h := reflection_log_14664_neg
  have he : Real.log (318697 / 200000) = -Real.log (200000 / 318697) := by
    rw [show ((318697 / 200000) : ℝ) = ((200000 / 318697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14665_neg : (900134449 / 1000000000) ≤ -Real.log (81303 / 200000) ∧
    -Real.log (81303 / 200000) ≤ (900134451 / 1000000000) := by
  have h := checkLog_sound (w := (18697 / 181303)) (n := 12)
    (lo := (206987269 / 1000000000)) (hi := (20698727 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 81303) = 1/(81303 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14665 : Bounds (-900134451 / 1000000000) (-900134449 / 1000000000) (Real.log (81303 / 200000)) := by
  have h := reflection_log_14665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14666_neg : (18681043 / 40000000) ≤ -Real.log (1000000 / 1595243) ∧
    -Real.log (1000000 / 1595243) ≤ (116756519 / 250000000) := by
  have h := checkLog_sound (w := (595243 / 2595243)) (n := 12)
    (lo := (18681043 / 40000000)) (hi := (116756519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1595243 / 1000000) = 1/(1000000 / 1595243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14666 : Bounds (18681043 / 40000000) (116756519 / 250000000) (Real.log (1595243 / 1000000)) := by
  have h := reflection_log_14666_neg
  have he : Real.log (1595243 / 1000000) = -Real.log (1000000 / 1595243) := by
    rw [show ((1595243 / 1000000) : ℝ) = ((1000000 / 1595243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14667_neg : (904468391 / 1000000000) ≤ -Real.log (404757 / 1000000) ∧
    -Real.log (404757 / 1000000) ≤ (904468393 / 1000000000) := by
  have h := checkLog_sound (w := (95243 / 904757)) (n := 12)
    (lo := (211321211 / 1000000000)) (hi := (52830303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404757) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 404757) = 1/(404757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14667 : Bounds (-904468393 / 1000000000) (-904468391 / 1000000000) (Real.log (404757 / 1000000)) := by
  have h := reflection_log_14667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14668_neg : (109360579 / 250000000) ≤ -Real.log (645685770951 / 1000000000000) ∧
    -Real.log (645685770951 / 1000000000000) ≤ (437442317 / 1000000000) := by
  have h := checkLog_sound (w := (354314229049 / 1645685770951)) (n := 12)
    (lo := (109360579 / 250000000)) (hi := (437442317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 645685770951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 645685770951) = 1/(645685770951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14668 : Bounds (-437442317 / 1000000000) (-109360579 / 250000000) (Real.log (645685770951 / 1000000000000)) := by
  have h := reflection_log_14668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14669_neg : (6784547 / 15625000) ≤ -Real.log (25911022191 / 40000000000) ∧
    -Real.log (25911022191 / 40000000000) ≤ (434211009 / 1000000000) := by
  have h := checkLog_sound (w := (14088977809 / 65911022191)) (n := 12)
    (lo := (6784547 / 15625000)) (hi := (434211009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 25911022191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 25911022191) = 1/(25911022191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14669 : Bounds (-434211009 / 1000000000) (-6784547 / 15625000) (Real.log (25911022191 / 40000000000)) := by
  have h := reflection_log_14669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14670_neg : (1366057891 / 1000000000) ≤ -Real.log (25000000000 / 97996691389) ∧
    -Real.log (25000000000 / 97996691389) ≤ (1366057893 / 1000000000) := by
  have h := checkLog_sound (w := (47996691389 / 147996691389)) (n := 12)
    (lo := (672910711 / 1000000000)) (hi := (84113839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97996691389 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(97996691389 / 50000000000) = 1/(25000000000 / 97996691389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14670 : Bounds (1366057891 / 1000000000) (1366057893 / 1000000000) (Real.log (97996691389 / 25000000000)) := by
  have h := reflection_log_14670_neg
  have he : Real.log (97996691389 / 25000000000) = -Real.log (25000000000 / 97996691389) := by
    rw [show ((97996691389 / 25000000000) : ℝ) = ((25000000000 / 97996691389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14671_neg : (1371494467 / 1000000000) ≤ -Real.log (250000000000 / 985309086687) ∧
    -Real.log (250000000000 / 985309086687) ≤ (1371494469 / 1000000000) := by
  have h := checkLog_sound (w := (485309086687 / 1485309086687)) (n := 12)
    (lo := (678347287 / 1000000000)) (hi := (84793411 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985309086687 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(985309086687 / 500000000000) = 1/(250000000000 / 985309086687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14671 : Bounds (1371494467 / 1000000000) (1371494469 / 1000000000) (Real.log (985309086687 / 250000000000)) := by
  have h := reflection_log_14671_neg
  have he : Real.log (985309086687 / 250000000000) = -Real.log (250000000000 / 985309086687) := by
    rw [show ((985309086687 / 250000000000) : ℝ) = ((250000000000 / 985309086687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14672_neg : (3684277039 / 1000000000) ≤ -Real.log (250000000000 / 9954081632653) ∧
    -Real.log (250000000000 / 9954081632653) ≤ (736855409 / 200000000) := by
  have h := checkLog_sound (w := (1954081632653 / 17954081632653)) (n := 12)
    (lo := (218541139 / 1000000000)) (hi := (10927057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9954081632653 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9954081632653 / 8000000000000) = 1/(250000000000 / 9954081632653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14672 : Bounds (3684277039 / 1000000000) (736855409 / 200000000) (Real.log (9954081632653 / 250000000000)) := by
  have h := reflection_log_14672_neg
  have he : Real.log (9954081632653 / 250000000000) = -Real.log (250000000000 / 9954081632653) := by
    rw [show ((9954081632653 / 250000000000) : ℝ) = ((250000000000 / 9954081632653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14673_neg : (3705408753 / 1000000000) ≤ -Real.log (250000000000 / 10166666666667) ∧
    -Real.log (250000000000 / 10166666666667) ≤ (3705408759 / 1000000000) := by
  have h := checkLog_sound (w := (2166666666667 / 18166666666667)) (n := 12)
    (lo := (239672853 / 1000000000)) (hi := (119836427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10166666666667 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10166666666667 / 8000000000000) = 1/(250000000000 / 10166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14673 : Bounds (3705408753 / 1000000000) (3705408759 / 1000000000) (Real.log (10166666666667 / 250000000000)) := by
  have h := reflection_log_14673_neg
  have he : Real.log (10166666666667 / 250000000000) = -Real.log (250000000000 / 10166666666667) := by
    rw [show ((10166666666667 / 250000000000) : ℝ) = ((250000000000 / 10166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14674_neg : (669366651 / 1000000000) ≤ -Real.log (1000 / 1953) ∧
    -Real.log (1000 / 1953) ≤ (167341663 / 250000000) := by
  have h := checkLog_sound (w := (953 / 2953)) (n := 12)
    (lo := (669366651 / 1000000000)) (hi := (167341663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1953 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1953 / 1000) = 1/(1000 / 1953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14674 : Bounds (669366651 / 1000000000) (167341663 / 250000000) (Real.log (1953 / 1000)) := by
  have h := reflection_log_14674_neg
  have he : Real.log (1953 / 1000) = -Real.log (1000 / 1953) := by
    rw [show ((1953 / 1000) : ℝ) = ((1000 / 1953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14675_neg : (122304307 / 40000000) ≤ -Real.log (47 / 1000) ∧
    -Real.log (47 / 1000) ≤ (1194378 / 390625) := by
  have h := checkLog_sound (w := (31 / 219)) (n := 12)
    (lo := (57003791 / 200000000)) (hi := (71254739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 94) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 94) = 1/(47 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14675 : Bounds (-1194378 / 390625) (-122304307 / 40000000) (Real.log (47 / 1000)) := by
  have h := reflection_log_14675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14676_neg : (476273 / 500000000) ≤ -Real.log (1000000 / 1000953) ∧
    -Real.log (1000000 / 1000953) ≤ (952547 / 1000000000) := by
  have h := checkLog_sound (w := (953 / 2000953)) (n := 12)
    (lo := (476273 / 500000000)) (hi := (952547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000953 / 1000000) = 1/(1000000 / 1000953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14676 : Bounds (476273 / 500000000) (952547 / 1000000000) (Real.log (1000953 / 1000000)) := by
  have h := reflection_log_14676_neg
  have he : Real.log (1000953 / 1000000) = -Real.log (1000000 / 1000953) := by
    rw [show ((1000953 / 1000000) : ℝ) = ((1000000 / 1000953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14677_neg : (476727 / 500000000) ≤ -Real.log (999047 / 1000000) ∧
    -Real.log (999047 / 1000000) ≤ (190691 / 200000000) := by
  have h := checkLog_sound (w := (953 / 1999047)) (n := 12)
    (lo := (476727 / 500000000)) (hi := (190691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999047) = 1/(999047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14677 : Bounds (-190691 / 200000000) (-476727 / 500000000) (Real.log (999047 / 1000000)) := by
  have h := reflection_log_14677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14678_neg : (466612887 / 1000000000) ≤ -Real.log (125000 / 199323) ∧
    -Real.log (125000 / 199323) ≤ (58326611 / 125000000) := by
  have h := checkLog_sound (w := (74323 / 324323)) (n := 12)
    (lo := (466612887 / 1000000000)) (hi := (58326611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199323 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199323 / 125000) = 1/(125000 / 199323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14678 : Bounds (466612887 / 1000000000) (58326611 / 125000000) (Real.log (199323 / 125000)) := by
  have h := reflection_log_14678_neg
  have he : Real.log (199323 / 125000) = -Real.log (125000 / 199323) := by
    rw [show ((199323 / 125000) : ℝ) = ((125000 / 199323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14679_neg : (902841577 / 1000000000) ≤ -Real.log (50677 / 125000) ∧
    -Real.log (50677 / 125000) ≤ (902841579 / 1000000000) := by
  have h := checkLog_sound (w := (11823 / 113177)) (n := 12)
    (lo := (209694397 / 1000000000)) (hi := (104847199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50677) = 1/(50677 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14679 : Bounds (-902841579 / 1000000000) (-902841577 / 1000000000) (Real.log (50677 / 125000)) := by
  have h := reflection_log_14679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14680_neg : (467717267 / 1000000000) ≤ -Real.log (500000 / 798173) ∧
    -Real.log (500000 / 798173) ≤ (116929317 / 250000000) := by
  have h := checkLog_sound (w := (298173 / 1298173)) (n := 12)
    (lo := (467717267 / 1000000000)) (hi := (116929317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798173 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798173 / 500000) = 1/(500000 / 798173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14680 : Bounds (467717267 / 1000000000) (116929317 / 250000000) (Real.log (798173 / 500000)) := by
  have h := reflection_log_14680_neg
  have he : Real.log (798173 / 500000) = -Real.log (500000 / 798173) := by
    rw [show ((798173 / 500000) : ℝ) = ((500000 / 798173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14681_neg : (907197203 / 1000000000) ≤ -Real.log (201827 / 500000) ∧
    -Real.log (201827 / 500000) ≤ (181439441 / 200000000) := by
  have h := checkLog_sound (w := (48173 / 451827)) (n := 12)
    (lo := (214050023 / 1000000000)) (hi := (26756253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201827) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 201827) = 1/(201827 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14681 : Bounds (-181439441 / 200000000) (-907197203 / 1000000000) (Real.log (201827 / 500000)) := by
  have h := reflection_log_14681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14682_neg : (3433437 / 7812500) ≤ -Real.log (161092862071 / 250000000000) ∧
    -Real.log (161092862071 / 250000000000) ≤ (439479937 / 1000000000) := by
  have h := checkLog_sound (w := (88907137929 / 411092862071)) (n := 12)
    (lo := (3433437 / 7812500)) (hi := (439479937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 161092862071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 161092862071) = 1/(161092862071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14682 : Bounds (-439479937 / 1000000000) (-3433437 / 7812500) (Real.log (161092862071 / 250000000000)) := by
  have h := reflection_log_14682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14683_neg : (436228691 / 1000000000) ≤ -Real.log (10101091671 / 15625000000) ∧
    -Real.log (10101091671 / 15625000000) ≤ (109057173 / 250000000) := by
  have h := checkLog_sound (w := (5523908329 / 25726091671)) (n := 12)
    (lo := (436228691 / 1000000000)) (hi := (109057173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10101091671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10101091671) = 1/(10101091671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14683 : Bounds (-109057173 / 250000000) (-436228691 / 1000000000) (Real.log (10101091671 / 15625000000)) := by
  have h := reflection_log_14683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14684_neg : (273890893 / 200000000) ≤ -Real.log (500000000000 / 1966602206129) ∧
    -Real.log (500000000000 / 1966602206129) ≤ (1369454467 / 1000000000) := by
  have h := checkLog_sound (w := (966602206129 / 2966602206129)) (n := 12)
    (lo := (135261457 / 200000000)) (hi := (338153643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966602206129 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1966602206129 / 1000000000000) = 1/(500000000000 / 1966602206129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14684 : Bounds (273890893 / 200000000) (1369454467 / 1000000000) (Real.log (1966602206129 / 500000000000)) := by
  have h := reflection_log_14684_neg
  have he : Real.log (1966602206129 / 500000000000) = -Real.log (500000000000 / 1966602206129) := by
    rw [show ((1966602206129 / 500000000000) : ℝ) = ((500000000000 / 1966602206129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14685_neg : (137491447 / 100000000) ≤ -Real.log (250000000000 / 988684616033) ∧
    -Real.log (250000000000 / 988684616033) ≤ (171864309 / 125000000) := by
  have h := checkLog_sound (w := (488684616033 / 1488684616033)) (n := 12)
    (lo := (68176729 / 100000000)) (hi := (681767291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988684616033 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(988684616033 / 500000000000) = 1/(250000000000 / 988684616033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14685 : Bounds (137491447 / 100000000) (171864309 / 125000000) (Real.log (988684616033 / 250000000000)) := by
  have h := reflection_log_14685_neg
  have he : Real.log (988684616033 / 250000000000) = -Real.log (250000000000 / 988684616033) := by
    rw [show ((988684616033 / 250000000000) : ℝ) = ((250000000000 / 988684616033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14686_neg : (3705408753 / 1000000000) ≤ -Real.log (500000000000 / 20333333333333) ∧
    -Real.log (500000000000 / 20333333333333) ≤ (3705408759 / 1000000000) := by
  have h := checkLog_sound (w := (4333333333333 / 36333333333333)) (n := 12)
    (lo := (239672853 / 1000000000)) (hi := (119836427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20333333333333 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20333333333333 / 16000000000000) = 1/(500000000000 / 20333333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14686 : Bounds (3705408753 / 1000000000) (3705408759 / 1000000000) (Real.log (20333333333333 / 500000000000)) := by
  have h := reflection_log_14686_neg
  have he : Real.log (20333333333333 / 500000000000) = -Real.log (500000000000 / 20333333333333) := by
    rw [show ((20333333333333 / 500000000000) : ℝ) = ((500000000000 / 20333333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14687_neg : (1863487163 / 500000000) ≤ -Real.log (500000000000 / 20776595744681) ∧
    -Real.log (500000000000 / 20776595744681) ≤ (931743583 / 250000000) := by
  have h := checkLog_sound (w := (4776595744681 / 36776595744681)) (n := 12)
    (lo := (130619213 / 500000000)) (hi := (261238427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20776595744681 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20776595744681 / 16000000000000) = 1/(500000000000 / 20776595744681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14687 : Bounds (1863487163 / 500000000) (931743583 / 250000000) (Real.log (20776595744681 / 500000000000)) := by
  have h := reflection_log_14687_neg
  have he : Real.log (20776595744681 / 500000000000) = -Real.log (500000000000 / 20776595744681) := by
    rw [show ((20776595744681 / 500000000000) : ℝ) = ((500000000000 / 20776595744681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14688_neg : (669878553 / 1000000000) ≤ -Real.log (500 / 977) ∧
    -Real.log (500 / 977) ≤ (334939277 / 500000000) := by
  have h := checkLog_sound (w := (477 / 1477)) (n := 12)
    (lo := (669878553 / 1000000000)) (hi := (334939277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977 / 500) = 1/(500 / 977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14688 : Bounds (669878553 / 1000000000) (334939277 / 500000000) (Real.log (977 / 500)) := by
  have h := reflection_log_14688_neg
  have he : Real.log (977 / 500) = -Real.log (500 / 977) := by
    rw [show ((977 / 500) : ℝ) = ((500 / 977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14689_neg : (76977847 / 25000000) ≤ -Real.log (23 / 500) ∧
    -Real.log (23 / 500) ≤ (615822777 / 200000000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 92) = 1/(23 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14689 : Bounds (-615822777 / 200000000) (-76977847 / 25000000) (Real.log (23 / 500)) := by
  have h := reflection_log_14689_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14690_neg : (190709 / 200000000) ≤ -Real.log (500000 / 500477) ∧
    -Real.log (500000 / 500477) ≤ (476773 / 500000000) := by
  have h := checkLog_sound (w := (477 / 1000477)) (n := 12)
    (lo := (190709 / 200000000)) (hi := (476773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500477 / 500000) = 1/(500000 / 500477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14690 : Bounds (190709 / 200000000) (476773 / 500000000) (Real.log (500477 / 500000)) := by
  have h := reflection_log_14690_neg
  have he : Real.log (500477 / 500000) = -Real.log (500000 / 500477) := by
    rw [show ((500477 / 500000) : ℝ) = ((500000 / 500477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14691_neg : (190891 / 200000000) ≤ -Real.log (499523 / 500000) ∧
    -Real.log (499523 / 500000) ≤ (119307 / 125000000) := by
  have h := checkLog_sound (w := (477 / 999523)) (n := 12)
    (lo := (190891 / 200000000)) (hi := (119307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499523) = 1/(499523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14691 : Bounds (-119307 / 125000000) (-190891 / 200000000) (Real.log (499523 / 500000)) := by
  have h := reflection_log_14691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14692_neg : (467304991 / 1000000000) ≤ -Real.log (125000 / 199461) ∧
    -Real.log (125000 / 199461) ≤ (14603281 / 31250000) := by
  have h := checkLog_sound (w := (74461 / 324461)) (n := 12)
    (lo := (467304991 / 1000000000)) (hi := (14603281 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199461 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199461 / 125000) = 1/(125000 / 199461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14692 : Bounds (467304991 / 1000000000) (14603281 / 31250000) (Real.log (199461 / 125000)) := by
  have h := reflection_log_14692_neg
  have he : Real.log (199461 / 125000) = -Real.log (125000 / 199461) := by
    rw [show ((199461 / 125000) : ℝ) = ((125000 / 199461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14693_neg : (905568421 / 1000000000) ≤ -Real.log (50539 / 125000) ∧
    -Real.log (50539 / 125000) ≤ (905568423 / 1000000000) := by
  have h := checkLog_sound (w := (11961 / 113039)) (n := 12)
    (lo := (212421241 / 1000000000)) (hi := (106210621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50539) = 1/(50539 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14693 : Bounds (-905568423 / 1000000000) (-905568421 / 1000000000) (Real.log (50539 / 125000)) := by
  have h := reflection_log_14693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14694_neg : (468411111 / 1000000000) ≤ -Real.log (500000 / 798727) ∧
    -Real.log (500000 / 798727) ≤ (58551389 / 125000000) := by
  have h := checkLog_sound (w := (298727 / 1298727)) (n := 12)
    (lo := (468411111 / 1000000000)) (hi := (58551389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798727 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798727 / 500000) = 1/(500000 / 798727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14694 : Bounds (468411111 / 1000000000) (58551389 / 125000000) (Real.log (798727 / 500000)) := by
  have h := reflection_log_14694_neg
  have he : Real.log (798727 / 500000) = -Real.log (500000 / 798727) := by
    rw [show ((798727 / 500000) : ℝ) = ((500000 / 798727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14695_neg : (454972951 / 500000000) ≤ -Real.log (201273 / 500000) ∧
    -Real.log (201273 / 500000) ≤ (56871619 / 62500000) := by
  have h := checkLog_sound (w := (48727 / 451273)) (n := 12)
    (lo := (108399361 / 500000000)) (hi := (216798723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201273) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 201273) = 1/(201273 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14695 : Bounds (-56871619 / 62500000) (-454972951 / 500000000) (Real.log (201273 / 500000)) := by
  have h := reflection_log_14695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14696_neg : (441534791 / 1000000000) ≤ -Real.log (160762179471 / 250000000000) ∧
    -Real.log (160762179471 / 250000000000) ≤ (55191849 / 125000000) := by
  have h := checkLog_sound (w := (89237820529 / 410762179471)) (n := 12)
    (lo := (441534791 / 1000000000)) (hi := (55191849 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 160762179471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 160762179471) = 1/(160762179471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14696 : Bounds (-55191849 / 125000000) (-441534791 / 1000000000) (Real.log (160762179471 / 250000000000)) := by
  have h := reflection_log_14696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14697_neg : (43826343 / 100000000) ≤ -Real.log (10080559479 / 15625000000) ∧
    -Real.log (10080559479 / 15625000000) ≤ (438263431 / 1000000000) := by
  have h := checkLog_sound (w := (5544440521 / 25705559479)) (n := 12)
    (lo := (43826343 / 100000000)) (hi := (438263431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10080559479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10080559479) = 1/(10080559479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14697 : Bounds (-438263431 / 1000000000) (-43826343 / 100000000) (Real.log (10080559479 / 15625000000)) := by
  have h := reflection_log_14697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14698_neg : (343218353 / 250000000) ≤ -Real.log (62500000000 / 246667177823) ∧
    -Real.log (62500000000 / 246667177823) ≤ (686436707 / 500000000) := by
  have h := checkLog_sound (w := (121667177823 / 371667177823)) (n := 12)
    (lo := (84965779 / 125000000)) (hi := (679726233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246667177823 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(246667177823 / 125000000000) = 1/(62500000000 / 246667177823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14698 : Bounds (343218353 / 250000000) (686436707 / 500000000) (Real.log (246667177823 / 62500000000)) := by
  have h := reflection_log_14698_neg
  have he : Real.log (246667177823 / 62500000000) = -Real.log (62500000000 / 246667177823) := by
    rw [show ((246667177823 / 62500000000) : ℝ) = ((62500000000 / 246667177823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14699_neg : (689178507 / 500000000) ≤ -Real.log (250000000000 / 992094071237) ∧
    -Real.log (250000000000 / 992094071237) ≤ (172294627 / 125000000) := by
  have h := checkLog_sound (w := (492094071237 / 1492094071237)) (n := 12)
    (lo := (342604917 / 500000000)) (hi := (137041967 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((992094071237 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(992094071237 / 500000000000) = 1/(250000000000 / 992094071237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14699 : Bounds (689178507 / 500000000) (172294627 / 125000000) (Real.log (992094071237 / 250000000000)) := by
  have h := reflection_log_14699_neg
  have he : Real.log (992094071237 / 250000000000) = -Real.log (250000000000 / 992094071237) := by
    rw [show ((992094071237 / 250000000000) : ℝ) = ((250000000000 / 992094071237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14700_neg : (1863487163 / 500000000) ≤ -Real.log (12500000000 / 519414893617) ∧
    -Real.log (12500000000 / 519414893617) ≤ (931743583 / 250000000) := by
  have h := checkLog_sound (w := (119414893617 / 919414893617)) (n := 12)
    (lo := (130619213 / 500000000)) (hi := (261238427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519414893617 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(519414893617 / 400000000000) = 1/(12500000000 / 519414893617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14700 : Bounds (1863487163 / 500000000) (931743583 / 250000000) (Real.log (519414893617 / 12500000000)) := by
  have h := reflection_log_14700_neg
  have he : Real.log (519414893617 / 12500000000) = -Real.log (12500000000 / 519414893617) := by
    rw [show ((519414893617 / 12500000000) : ℝ) = ((12500000000 / 519414893617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14701_neg : (3748992433 / 1000000000) ≤ -Real.log (500000000000 / 21239130434783) ∧
    -Real.log (500000000000 / 21239130434783) ≤ (3748992439 / 1000000000) := by
  have h := checkLog_sound (w := (5239130434783 / 37239130434783)) (n := 12)
    (lo := (283256533 / 1000000000)) (hi := (141628267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21239130434783 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21239130434783 / 16000000000000) = 1/(500000000000 / 21239130434783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14701 : Bounds (3748992433 / 1000000000) (3748992439 / 1000000000) (Real.log (21239130434783 / 500000000000)) := by
  have h := reflection_log_14701_neg
  have he : Real.log (21239130434783 / 500000000000) = -Real.log (500000000000 / 21239130434783) := by
    rw [show ((21239130434783 / 500000000000) : ℝ) = ((500000000000 / 21239130434783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14702_neg : (670390193 / 1000000000) ≤ -Real.log (200 / 391) ∧
    -Real.log (200 / 391) ≤ (335195097 / 500000000) := by
  have h := checkLog_sound (w := (191 / 591)) (n := 12)
    (lo := (670390193 / 1000000000)) (hi := (335195097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391 / 200) = 1/(200 / 391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14702 : Bounds (670390193 / 1000000000) (335195097 / 500000000) (Real.log (391 / 200)) := by
  have h := reflection_log_14702_neg
  have he : Real.log (391 / 200) = -Real.log (200 / 391) := by
    rw [show ((391 / 200) : ℝ) = ((200 / 391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14703_neg : (1550546393 / 500000000) ≤ -Real.log (9 / 200) ∧
    -Real.log (9 / 200) ≤ (3101092791 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 43)) (n := 12)
    (lo := (164252033 / 500000000)) (hi := (328504067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 18) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 18) = 1/(9 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14703 : Bounds (-3101092791 / 1000000000) (-1550546393 / 500000000) (Real.log (9 / 200)) := by
  have h := reflection_log_14703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14704_neg : (59659 / 62500000) ≤ -Real.log (200000 / 200191) ∧
    -Real.log (200000 / 200191) ≤ (190909 / 200000000) := by
  have h := checkLog_sound (w := (191 / 400191)) (n := 12)
    (lo := (59659 / 62500000)) (hi := (190909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200191 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200191 / 200000) = 1/(200000 / 200191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14704 : Bounds (59659 / 62500000) (190909 / 200000000) (Real.log (200191 / 200000)) := by
  have h := reflection_log_14704_neg
  have he : Real.log (200191 / 200000) = -Real.log (200000 / 200191) := by
    rw [show ((200191 / 200000) : ℝ) = ((200000 / 200191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14705_neg : (14929 / 15625000) ≤ -Real.log (199809 / 200000) ∧
    -Real.log (199809 / 200000) ≤ (955457 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 399809)) (n := 12)
    (lo := (14929 / 15625000)) (hi := (955457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199809) = 1/(199809 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14705 : Bounds (-955457 / 1000000000) (-14929 / 15625000) (Real.log (199809 / 200000)) := by
  have h := reflection_log_14705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14706_neg : (467999747 / 1000000000) ≤ -Real.log (1000000 / 1596797) ∧
    -Real.log (1000000 / 1596797) ≤ (116999937 / 250000000) := by
  have h := checkLog_sound (w := (596797 / 2596797)) (n := 12)
    (lo := (467999747 / 1000000000)) (hi := (116999937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1596797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1596797 / 1000000) = 1/(1000000 / 1596797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14706 : Bounds (467999747 / 1000000000) (116999937 / 250000000) (Real.log (1596797 / 1000000)) := by
  have h := reflection_log_14706_neg
  have he : Real.log (1596797 / 1000000) = -Real.log (1000000 / 1596797) := by
    rw [show ((1596797 / 1000000) : ℝ) = ((1000000 / 1596797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14707_neg : (908315121 / 1000000000) ≤ -Real.log (403203 / 1000000) ∧
    -Real.log (403203 / 1000000) ≤ (908315123 / 1000000000) := by
  have h := checkLog_sound (w := (96797 / 903203)) (n := 12)
    (lo := (215167941 / 1000000000)) (hi := (107583971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 403203) = 1/(403203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14707 : Bounds (-908315123 / 1000000000) (-908315121 / 1000000000) (Real.log (403203 / 1000000)) := by
  have h := reflection_log_14707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14708_neg : (117277057 / 250000000) ≤ -Real.log (125000 / 199821) ∧
    -Real.log (125000 / 199821) ≤ (469108229 / 1000000000) := by
  have h := checkLog_sound (w := (74821 / 324821)) (n := 12)
    (lo := (117277057 / 250000000)) (hi := (469108229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199821 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199821 / 125000) = 1/(125000 / 199821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14708 : Bounds (117277057 / 250000000) (469108229 / 1000000000) (Real.log (199821 / 125000)) := by
  have h := reflection_log_14708_neg
  have he : Real.log (199821 / 125000) = -Real.log (125000 / 199821) := by
    rw [show ((199821 / 125000) : ℝ) = ((125000 / 199821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14709_neg : (228179281 / 250000000) ≤ -Real.log (50179 / 125000) ∧
    -Real.log (50179 / 125000) ≤ (456358563 / 500000000) := by
  have h := checkLog_sound (w := (12321 / 112679)) (n := 12)
    (lo := (27446243 / 125000000)) (hi := (43913989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50179) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50179) = 1/(50179 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14709 : Bounds (-456358563 / 500000000) (-228179281 / 250000000) (Real.log (50179 / 125000)) := by
  have h := reflection_log_14709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14710_neg : (6931389 / 15625000) ≤ -Real.log (10026817959 / 15625000000) ∧
    -Real.log (10026817959 / 15625000000) ≤ (443608897 / 1000000000) := by
  have h := checkLog_sound (w := (5598182041 / 25651817959)) (n := 12)
    (lo := (6931389 / 15625000)) (hi := (443608897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10026817959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10026817959) = 1/(10026817959 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14710 : Bounds (-443608897 / 1000000000) (-6931389 / 15625000) (Real.log (10026817959 / 15625000000)) := by
  have h := reflection_log_14710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14711_neg : (440315373 / 1000000000) ≤ -Real.log (643833340791 / 1000000000000) ∧
    -Real.log (643833340791 / 1000000000000) ≤ (220157687 / 500000000) := by
  have h := checkLog_sound (w := (356166659209 / 1643833340791)) (n := 12)
    (lo := (440315373 / 1000000000)) (hi := (220157687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 643833340791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 643833340791) = 1/(643833340791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14711 : Bounds (-220157687 / 500000000) (-440315373 / 1000000000) (Real.log (643833340791 / 1000000000000)) := by
  have h := reflection_log_14711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14712_neg : (1376314869 / 1000000000) ≤ -Real.log (250000000000 / 990070138367) ∧
    -Real.log (250000000000 / 990070138367) ≤ (1376314871 / 1000000000) := by
  have h := checkLog_sound (w := (490070138367 / 1490070138367)) (n := 12)
    (lo := (683167689 / 1000000000)) (hi := (68316769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990070138367 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(990070138367 / 500000000000) = 1/(250000000000 / 990070138367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14712 : Bounds (1376314869 / 1000000000) (1376314871 / 1000000000) (Real.log (990070138367 / 250000000000)) := by
  have h := reflection_log_14712_neg
  have he : Real.log (990070138367 / 250000000000) = -Real.log (250000000000 / 990070138367) := by
    rw [show ((990070138367 / 250000000000) : ℝ) = ((250000000000 / 990070138367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14713_neg : (172728169 / 125000000) ≤ -Real.log (500000000000 / 1991081926703) ∧
    -Real.log (500000000000 / 1991081926703) ≤ (690912677 / 500000000) := by
  have h := checkLog_sound (w := (991081926703 / 2991081926703)) (n := 12)
    (lo := (172169543 / 250000000)) (hi := (688678173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1991081926703 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1991081926703 / 1000000000000) = 1/(500000000000 / 1991081926703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14713 : Bounds (172728169 / 125000000) (690912677 / 500000000) (Real.log (1991081926703 / 500000000000)) := by
  have h := reflection_log_14713_neg
  have he : Real.log (1991081926703 / 500000000000) = -Real.log (500000000000 / 1991081926703) := by
    rw [show ((1991081926703 / 500000000000) : ℝ) = ((500000000000 / 1991081926703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14714_neg : (3748992433 / 1000000000) ≤ -Real.log (250000000000 / 10619565217391) ∧
    -Real.log (250000000000 / 10619565217391) ≤ (3748992439 / 1000000000) := by
  have h := checkLog_sound (w := (2619565217391 / 18619565217391)) (n := 12)
    (lo := (283256533 / 1000000000)) (hi := (141628267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10619565217391 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10619565217391 / 8000000000000) = 1/(250000000000 / 10619565217391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14714 : Bounds (3748992433 / 1000000000) (3748992439 / 1000000000) (Real.log (10619565217391 / 250000000000)) := by
  have h := reflection_log_14714_neg
  have he : Real.log (10619565217391 / 250000000000) = -Real.log (250000000000 / 10619565217391) := by
    rw [show ((10619565217391 / 250000000000) : ℝ) = ((250000000000 / 10619565217391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14715_neg : (3771482979 / 1000000000) ≤ -Real.log (500000000000 / 21722222222223) ∧
    -Real.log (500000000000 / 21722222222223) ≤ (754296597 / 200000000) := by
  have h := checkLog_sound (w := (5722222222223 / 37722222222223)) (n := 12)
    (lo := (305747079 / 1000000000)) (hi := (7643677 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21722222222223 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21722222222223 / 16000000000000) = 1/(500000000000 / 21722222222223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14715 : Bounds (3771482979 / 1000000000) (754296597 / 200000000) (Real.log (21722222222223 / 500000000000)) := by
  have h := reflection_log_14715_neg
  have he : Real.log (21722222222223 / 500000000000) = -Real.log (500000000000 / 21722222222223) := by
    rw [show ((21722222222223 / 500000000000) : ℝ) = ((500000000000 / 21722222222223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14716_neg : (670901571 / 1000000000) ≤ -Real.log (250 / 489) ∧
    -Real.log (250 / 489) ≤ (167725393 / 250000000) := by
  have h := checkLog_sound (w := (239 / 739)) (n := 12)
    (lo := (670901571 / 1000000000)) (hi := (167725393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489 / 250) = 1/(250 / 489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14716 : Bounds (670901571 / 1000000000) (167725393 / 250000000) (Real.log (489 / 250)) := by
  have h := reflection_log_14716_neg
  have he : Real.log (489 / 250) = -Real.log (250 / 489) := by
    rw [show ((489 / 250) : ℝ) = ((250 / 489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14717_neg : (1561782821 / 500000000) ≤ -Real.log (11 / 250) ∧
    -Real.log (11 / 250) ≤ (3123565647 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 88) = 1/(11 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14717 : Bounds (-3123565647 / 1000000000) (-1561782821 / 500000000) (Real.log (11 / 250)) := by
  have h := reflection_log_14717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14718_neg : (955543 / 1000000000) ≤ -Real.log (250000 / 250239) ∧
    -Real.log (250000 / 250239) ≤ (119443 / 125000000) := by
  have h := checkLog_sound (w := (239 / 500239)) (n := 12)
    (lo := (955543 / 1000000000)) (hi := (119443 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250239 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250239 / 250000) = 1/(250000 / 250239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14718 : Bounds (955543 / 1000000000) (119443 / 125000000) (Real.log (250239 / 250000)) := by
  have h := reflection_log_14718_neg
  have he : Real.log (250239 / 250000) = -Real.log (250000 / 250239) := by
    rw [show ((250239 / 250000) : ℝ) = ((250000 / 250239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14719_neg : (956457 / 1000000000) ≤ -Real.log (249761 / 250000) ∧
    -Real.log (249761 / 250000) ≤ (478229 / 500000000) := by
  have h := checkLog_sound (w := (239 / 499761)) (n := 12)
    (lo := (956457 / 1000000000)) (hi := (478229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249761) = 1/(249761 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14719 : Bounds (-478229 / 500000000) (-956457 / 1000000000) (Real.log (249761 / 250000)) := by
  have h := reflection_log_14719_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0230 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14720_neg : (18747861 / 40000000) ≤ -Real.log (100000 / 159791) ∧
    -Real.log (100000 / 159791) ≤ (234348263 / 500000000) := by
  have h := checkLog_sound (w := (59791 / 259791)) (n := 12)
    (lo := (18747861 / 40000000)) (hi := (234348263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159791 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159791 / 100000) = 1/(100000 / 159791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14720 : Bounds (18747861 / 40000000) (234348263 / 500000000) (Real.log (159791 / 100000)) := by
  have h := reflection_log_14720_neg
  have he : Real.log (159791 / 100000) = -Real.log (100000 / 159791) := by
    rw [show ((159791 / 100000) : ℝ) = ((100000 / 159791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14721_neg : (455539667 / 500000000) ≤ -Real.log (40209 / 100000) ∧
    -Real.log (40209 / 100000) ≤ (113884917 / 125000000) := by
  have h := checkLog_sound (w := (9791 / 90209)) (n := 12)
    (lo := (108966077 / 500000000)) (hi := (43586431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 40209) = 1/(40209 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14721 : Bounds (-113884917 / 125000000) (-455539667 / 500000000) (Real.log (40209 / 100000)) := by
  have h := reflection_log_14721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14722_neg : (469807359 / 1000000000) ≤ -Real.log (500000 / 799843) ∧
    -Real.log (500000 / 799843) ≤ (367037 / 781250) := by
  have h := checkLog_sound (w := (299843 / 1299843)) (n := 12)
    (lo := (469807359 / 1000000000)) (hi := (367037 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799843 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799843 / 500000) = 1/(500000 / 799843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14722 : Bounds (469807359 / 1000000000) (367037 / 781250) (Real.log (799843 / 500000)) := by
  have h := reflection_log_14722_neg
  have he : Real.log (799843 / 500000) = -Real.log (500000 / 799843) := by
    rw [show ((799843 / 500000) : ℝ) = ((500000 / 799843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14723_neg : (915506039 / 1000000000) ≤ -Real.log (200157 / 500000) ∧
    -Real.log (200157 / 500000) ≤ (915506041 / 1000000000) := by
  have h := checkLog_sound (w := (49843 / 450157)) (n := 12)
    (lo := (222358859 / 1000000000)) (hi := (11117943 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 200157) = 1/(200157 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14723 : Bounds (-915506041 / 1000000000) (-915506039 / 1000000000) (Real.log (200157 / 500000)) := by
  have h := reflection_log_14723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14724_neg : (445698679 / 1000000000) ≤ -Real.log (160094175351 / 250000000000) ∧
    -Real.log (160094175351 / 250000000000) ≤ (11142467 / 25000000) := by
  have h := checkLog_sound (w := (89905824649 / 410094175351)) (n := 12)
    (lo := (445698679 / 1000000000)) (hi := (11142467 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 160094175351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 160094175351) = 1/(160094175351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14724 : Bounds (-11142467 / 25000000) (-445698679 / 1000000000) (Real.log (160094175351 / 250000000000)) := by
  have h := reflection_log_14724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14725_neg : (442382809 / 1000000000) ≤ -Real.log (6425036319 / 10000000000) ∧
    -Real.log (6425036319 / 10000000000) ≤ (44238281 / 100000000) := by
  have h := checkLog_sound (w := (3574963681 / 16425036319)) (n := 12)
    (lo := (442382809 / 1000000000)) (hi := (44238281 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6425036319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6425036319) = 1/(6425036319 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14725 : Bounds (-44238281 / 100000000) (-442382809 / 1000000000) (Real.log (6425036319 / 10000000000)) := by
  have h := reflection_log_14725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14726_neg : (1379775859 / 1000000000) ≤ -Real.log (500000000000 / 1987005396801) ∧
    -Real.log (500000000000 / 1987005396801) ≤ (1379775861 / 1000000000) := by
  have h := checkLog_sound (w := (987005396801 / 2987005396801)) (n := 12)
    (lo := (686628679 / 1000000000)) (hi := (17165717 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987005396801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1987005396801 / 1000000000000) = 1/(500000000000 / 1987005396801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14726 : Bounds (1379775859 / 1000000000) (1379775861 / 1000000000) (Real.log (1987005396801 / 500000000000)) := by
  have h := reflection_log_14726_neg
  have he : Real.log (1987005396801 / 500000000000) = -Real.log (500000000000 / 1987005396801) := by
    rw [show ((1987005396801 / 500000000000) : ℝ) = ((500000000000 / 1987005396801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14727_neg : (1385313399 / 1000000000) ≤ -Real.log (100000000000 / 399607807871) ∧
    -Real.log (100000000000 / 399607807871) ≤ (1385313401 / 1000000000) := by
  have h := checkLog_sound (w := (199607807871 / 599607807871)) (n := 12)
    (lo := (692166219 / 1000000000)) (hi := (34608311 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399607807871 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(399607807871 / 200000000000) = 1/(100000000000 / 399607807871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14727 : Bounds (1385313399 / 1000000000) (1385313401 / 1000000000) (Real.log (399607807871 / 100000000000)) := by
  have h := reflection_log_14727_neg
  have he : Real.log (399607807871 / 100000000000) = -Real.log (100000000000 / 399607807871) := by
    rw [show ((399607807871 / 100000000000) : ℝ) = ((100000000000 / 399607807871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14728_neg : (3771482979 / 1000000000) ≤ -Real.log (250000000000 / 10861111111111) ∧
    -Real.log (250000000000 / 10861111111111) ≤ (754296597 / 200000000) := by
  have h := checkLog_sound (w := (2861111111111 / 18861111111111)) (n := 12)
    (lo := (305747079 / 1000000000)) (hi := (7643677 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10861111111111 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10861111111111 / 8000000000000) = 1/(250000000000 / 10861111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14728 : Bounds (3771482979 / 1000000000) (754296597 / 200000000) (Real.log (10861111111111 / 250000000000)) := by
  have h := reflection_log_14728_neg
  have he : Real.log (10861111111111 / 250000000000) = -Real.log (250000000000 / 10861111111111) := by
    rw [show ((10861111111111 / 250000000000) : ℝ) = ((250000000000 / 10861111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14729_neg : (3794467213 / 1000000000) ≤ -Real.log (500000000000 / 22227272727273) ∧
    -Real.log (500000000000 / 22227272727273) ≤ (3794467219 / 1000000000) := by
  have h := checkLog_sound (w := (6227272727273 / 38227272727273)) (n := 12)
    (lo := (328731313 / 1000000000)) (hi := (164365657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22227272727273 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22227272727273 / 16000000000000) = 1/(500000000000 / 22227272727273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14729 : Bounds (3794467213 / 1000000000) (3794467219 / 1000000000) (Real.log (22227272727273 / 500000000000)) := by
  have h := reflection_log_14729_neg
  have he : Real.log (22227272727273 / 500000000000) = -Real.log (500000000000 / 22227272727273) := by
    rw [show ((22227272727273 / 500000000000) : ℝ) = ((500000000000 / 22227272727273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14730_neg : (41963293 / 62500000) ≤ -Real.log (1000 / 1957) ∧
    -Real.log (1000 / 1957) ≤ (671412689 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 2957)) (n := 12)
    (lo := (41963293 / 62500000)) (hi := (671412689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957 / 1000) = 1/(1000 / 1957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14730 : Bounds (41963293 / 62500000) (671412689 / 1000000000) (Real.log (1957 / 1000)) := by
  have h := reflection_log_14730_neg
  have he : Real.log (1957 / 1000) = -Real.log (1000 / 1957) := by
    rw [show ((1957 / 1000) : ℝ) = ((1000 / 1957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14731_neg : (3146555161 / 1000000000) ≤ -Real.log (43 / 1000) ∧
    -Real.log (43 / 1000) ≤ (1573277583 / 500000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 86) = 1/(43 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14731 : Bounds (-1573277583 / 500000000) (-3146555161 / 1000000000) (Real.log (43 / 1000)) := by
  have h := reflection_log_14731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14732_neg : (478271 / 500000000) ≤ -Real.log (1000000 / 1000957) ∧
    -Real.log (1000000 / 1000957) ≤ (956543 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 2000957)) (n := 12)
    (lo := (478271 / 500000000)) (hi := (956543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000957 / 1000000) = 1/(1000000 / 1000957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14732 : Bounds (478271 / 500000000) (956543 / 1000000000) (Real.log (1000957 / 1000000)) := by
  have h := reflection_log_14732_neg
  have he : Real.log (1000957 / 1000000) = -Real.log (1000000 / 1000957) := by
    rw [show ((1000957 / 1000000) : ℝ) = ((1000000 / 1000957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14733_neg : (478729 / 500000000) ≤ -Real.log (999043 / 1000000) ∧
    -Real.log (999043 / 1000000) ≤ (957459 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 1999043)) (n := 12)
    (lo := (478729 / 500000000)) (hi := (957459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999043) = 1/(999043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14733 : Bounds (-957459 / 1000000000) (-478729 / 500000000) (Real.log (999043 / 1000000)) := by
  have h := reflection_log_14733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14734_neg : (93879439 / 200000000) ≤ -Real.log (100000 / 159903) ∧
    -Real.log (100000 / 159903) ≤ (117349299 / 250000000) := by
  have h := checkLog_sound (w := (59903 / 259903)) (n := 12)
    (lo := (93879439 / 200000000)) (hi := (117349299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159903 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159903 / 100000) = 1/(100000 / 159903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14734 : Bounds (93879439 / 200000000) (117349299 / 250000000) (Real.log (159903 / 100000)) := by
  have h := reflection_log_14734_neg
  have he : Real.log (159903 / 100000) = -Real.log (100000 / 159903) := by
    rw [show ((159903 / 100000) : ℝ) = ((100000 / 159903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14735_neg : (456934333 / 500000000) ≤ -Real.log (40097 / 100000) ∧
    -Real.log (40097 / 100000) ≤ (228467167 / 250000000) := by
  have h := checkLog_sound (w := (9903 / 90097)) (n := 12)
    (lo := (110360743 / 500000000)) (hi := (220721487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 40097) = 1/(40097 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14735 : Bounds (-228467167 / 250000000) (-456934333 / 500000000) (Real.log (40097 / 100000)) := by
  have h := reflection_log_14735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14736_neg : (470509751 / 1000000000) ≤ -Real.log (100000 / 160081) ∧
    -Real.log (100000 / 160081) ≤ (58813719 / 125000000) := by
  have h := checkLog_sound (w := (60081 / 260081)) (n := 12)
    (lo := (470509751 / 1000000000)) (hi := (58813719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160081 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160081 / 100000) = 1/(100000 / 160081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14736 : Bounds (470509751 / 1000000000) (58813719 / 125000000) (Real.log (160081 / 100000)) := by
  have h := reflection_log_14736_neg
  have he : Real.log (160081 / 100000) = -Real.log (100000 / 160081) := by
    rw [show ((160081 / 100000) : ℝ) = ((100000 / 160081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14737_neg : (114789723 / 125000000) ≤ -Real.log (39919 / 100000) ∧
    -Real.log (39919 / 100000) ≤ (459158893 / 500000000) := by
  have h := checkLog_sound (w := (10081 / 89919)) (n := 12)
    (lo := (56292651 / 250000000)) (hi := (45034121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 39919) = 1/(39919 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14737 : Bounds (-459158893 / 500000000) (-114789723 / 125000000) (Real.log (39919 / 100000)) := by
  have h := reflection_log_14737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14738_neg : (447808033 / 1000000000) ≤ -Real.log (6390273439 / 10000000000) ∧
    -Real.log (6390273439 / 10000000000) ≤ (223904017 / 500000000) := by
  have h := checkLog_sound (w := (3609726561 / 16390273439)) (n := 12)
    (lo := (447808033 / 1000000000)) (hi := (223904017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6390273439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6390273439) = 1/(6390273439 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14738 : Bounds (-223904017 / 500000000) (-447808033 / 1000000000) (Real.log (6390273439 / 10000000000)) := by
  have h := reflection_log_14738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14739_neg : (27779467 / 62500000) ≤ -Real.log (6411630591 / 10000000000) ∧
    -Real.log (6411630591 / 10000000000) ≤ (444471473 / 1000000000) := by
  have h := checkLog_sound (w := (3588369409 / 16411630591)) (n := 12)
    (lo := (27779467 / 62500000)) (hi := (444471473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6411630591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6411630591) = 1/(6411630591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14739 : Bounds (-444471473 / 1000000000) (-27779467 / 62500000) (Real.log (6411630591 / 10000000000)) := by
  have h := reflection_log_14739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14740_neg : (691632931 / 500000000) ≤ -Real.log (500000000000 / 1993952165997) ∧
    -Real.log (500000000000 / 1993952165997) ≤ (172908233 / 125000000) := by
  have h := checkLog_sound (w := (993952165997 / 2993952165997)) (n := 12)
    (lo := (345059341 / 500000000)) (hi := (690118683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993952165997 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1993952165997 / 1000000000000) = 1/(500000000000 / 1993952165997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14740 : Bounds (691632931 / 500000000) (172908233 / 125000000) (Real.log (1993952165997 / 500000000000)) := by
  have h := reflection_log_14740_neg
  have he : Real.log (1993952165997 / 500000000000) = -Real.log (500000000000 / 1993952165997) := by
    rw [show ((1993952165997 / 500000000000) : ℝ) = ((500000000000 / 1993952165997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14741_neg : (694413767 / 500000000) ≤ -Real.log (100000000000 / 401014554473) ∧
    -Real.log (100000000000 / 401014554473) ≤ (1388827537 / 1000000000) := by
  have h := checkLog_sound (w := (1014554473 / 801014554473)) (n := 12)
    (lo := (1266587 / 500000000)) (hi := (101327 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401014554473 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(401014554473 / 400000000000) = 1/(100000000000 / 401014554473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14741 : Bounds (694413767 / 500000000) (1388827537 / 1000000000) (Real.log (401014554473 / 100000000000)) := by
  have h := reflection_log_14741_neg
  have he : Real.log (401014554473 / 100000000000) = -Real.log (100000000000 / 401014554473) := by
    rw [show ((401014554473 / 100000000000) : ℝ) = ((100000000000 / 401014554473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14742_neg : (3794467213 / 1000000000) ≤ -Real.log (62500000000 / 2778409090909) ∧
    -Real.log (62500000000 / 2778409090909) ≤ (3794467219 / 1000000000) := by
  have h := checkLog_sound (w := (778409090909 / 4778409090909)) (n := 12)
    (lo := (328731313 / 1000000000)) (hi := (164365657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2778409090909 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2778409090909 / 2000000000000) = 1/(62500000000 / 2778409090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14742 : Bounds (3794467213 / 1000000000) (3794467219 / 1000000000) (Real.log (2778409090909 / 62500000000)) := by
  have h := reflection_log_14742_neg
  have he : Real.log (2778409090909 / 62500000000) = -Real.log (62500000000 / 2778409090909) := by
    rw [show ((2778409090909 / 62500000000) : ℝ) = ((62500000000 / 2778409090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14743_neg : (477245981 / 125000000) ≤ -Real.log (500000000000 / 22755813953489) ∧
    -Real.log (500000000000 / 22755813953489) ≤ (1908983927 / 500000000) := by
  have h := checkLog_sound (w := (6755813953489 / 38755813953489)) (n := 12)
    (lo := (88057987 / 250000000)) (hi := (352231949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22755813953489 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22755813953489 / 16000000000000) = 1/(500000000000 / 22755813953489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14743 : Bounds (477245981 / 125000000) (1908983927 / 500000000) (Real.log (22755813953489 / 500000000000)) := by
  have h := reflection_log_14743_neg
  have he : Real.log (22755813953489 / 500000000000) = -Real.log (500000000000 / 22755813953489) := by
    rw [show ((22755813953489 / 500000000000) : ℝ) = ((500000000000 / 22755813953489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14744_neg : (83990443 / 125000000) ≤ -Real.log (500 / 979) ∧
    -Real.log (500 / 979) ≤ (134384709 / 200000000) := by
  have h := checkLog_sound (w := (479 / 1479)) (n := 12)
    (lo := (83990443 / 125000000)) (hi := (134384709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979 / 500) = 1/(500 / 979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14744 : Bounds (83990443 / 125000000) (134384709 / 200000000) (Real.log (979 / 500)) := by
  have h := reflection_log_14744_neg
  have he : Real.log (979 / 500) = -Real.log (500 / 979) := by
    rw [show ((979 / 500) : ℝ) = ((500 / 979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14745_neg : (1585042829 / 500000000) ≤ -Real.log (21 / 500) ∧
    -Real.log (21 / 500) ≤ (3170085663 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 209)) (n := 12)
    (lo := (198748469 / 500000000)) (hi := (397496939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 84) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 84) = 1/(21 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14745 : Bounds (-3170085663 / 1000000000) (-1585042829 / 500000000) (Real.log (21 / 500)) := by
  have h := reflection_log_14745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14746_neg : (957541 / 1000000000) ≤ -Real.log (500000 / 500479) ∧
    -Real.log (500000 / 500479) ≤ (478771 / 500000000) := by
  have h := checkLog_sound (w := (479 / 1000479)) (n := 12)
    (lo := (957541 / 1000000000)) (hi := (478771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500479 / 500000) = 1/(500000 / 500479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14746 : Bounds (957541 / 1000000000) (478771 / 500000000) (Real.log (500479 / 500000)) := by
  have h := reflection_log_14746_neg
  have he : Real.log (500479 / 500000) = -Real.log (500000 / 500479) := by
    rw [show ((500479 / 500000) : ℝ) = ((500000 / 500479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14747_neg : (958459 / 1000000000) ≤ -Real.log (499521 / 500000) ∧
    -Real.log (499521 / 500000) ≤ (47923 / 50000000) := by
  have h := checkLog_sound (w := (479 / 999521)) (n := 12)
    (lo := (958459 / 1000000000)) (hi := (47923 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499521) = 1/(499521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14747 : Bounds (-47923 / 50000000) (-958459 / 1000000000) (Real.log (499521 / 500000)) := by
  have h := reflection_log_14747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14748_neg : (235049937 / 500000000) ≤ -Real.log (500000 / 800077) ∧
    -Real.log (500000 / 800077) ≤ (3760799 / 8000000) := by
  have h := checkLog_sound (w := (300077 / 1300077)) (n := 12)
    (lo := (235049937 / 500000000)) (hi := (3760799 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800077 / 500000) = 1/(500000 / 800077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14748 : Bounds (235049937 / 500000000) (3760799 / 8000000) (Real.log (800077 / 500000)) := by
  have h := reflection_log_14748_neg
  have he : Real.log (800077 / 500000) = -Real.log (500000 / 800077) := by
    rw [show ((800077 / 500000) : ℝ) = ((500000 / 800077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14749_neg : (183335161 / 200000000) ≤ -Real.log (199923 / 500000) ∧
    -Real.log (199923 / 500000) ≤ (916675807 / 1000000000) := by
  have h := checkLog_sound (w := (50077 / 449923)) (n := 12)
    (lo := (1788229 / 8000000)) (hi := (111764313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199923) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 199923) = 1/(199923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14749 : Bounds (-916675807 / 1000000000) (-183335161 / 200000000) (Real.log (199923 / 500000)) := by
  have h := reflection_log_14749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14750_neg : (235607697 / 500000000) ≤ -Real.log (50000 / 80097) ∧
    -Real.log (50000 / 80097) ≤ (94243079 / 200000000) := by
  have h := checkLog_sound (w := (30097 / 130097)) (n := 12)
    (lo := (235607697 / 500000000)) (hi := (94243079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80097 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80097 / 50000) = 1/(50000 / 80097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14750 : Bounds (235607697 / 500000000) (94243079 / 200000000) (Real.log (80097 / 50000)) := by
  have h := reflection_log_14750_neg
  have he : Real.log (80097 / 50000) = -Real.log (50000 / 80097) := by
    rw [show ((80097 / 50000) : ℝ) = ((50000 / 80097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14751_neg : (92115253 / 100000000) ≤ -Real.log (19903 / 50000) ∧
    -Real.log (19903 / 50000) ≤ (230288133 / 250000000) := by
  have h := checkLog_sound (w := (5097 / 44903)) (n := 12)
    (lo := (4560107 / 20000000)) (hi := (228005351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19903) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 19903) = 1/(19903 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14751 : Bounds (-230288133 / 250000000) (-92115253 / 100000000) (Real.log (19903 / 50000)) := by
  have h := reflection_log_14751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14752_neg : (28121071 / 62500000) ≤ -Real.log (1594170591 / 2500000000) ∧
    -Real.log (1594170591 / 2500000000) ≤ (449937137 / 1000000000) := by
  have h := checkLog_sound (w := (905829409 / 4094170591)) (n := 12)
    (lo := (28121071 / 62500000)) (hi := (449937137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1594170591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1594170591) = 1/(1594170591 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14752 : Bounds (-449937137 / 1000000000) (-28121071 / 62500000) (Real.log (1594170591 / 2500000000)) := by
  have h := reflection_log_14752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14753_neg : (446575931 / 1000000000) ≤ -Real.log (159953794071 / 250000000000) ∧
    -Real.log (159953794071 / 250000000000) ≤ (111643983 / 250000000) := by
  have h := checkLog_sound (w := (90046205929 / 409953794071)) (n := 12)
    (lo := (446575931 / 1000000000)) (hi := (111643983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 159953794071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 159953794071) = 1/(159953794071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14753 : Bounds (-111643983 / 250000000) (-446575931 / 1000000000) (Real.log (159953794071 / 250000000000)) := by
  have h := reflection_log_14753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14754_neg : (1386775679 / 1000000000) ≤ -Real.log (100000000000 / 400192574141) ∧
    -Real.log (100000000000 / 400192574141) ≤ (693387841 / 500000000) := by
  have h := checkLog_sound (w := (192574141 / 800192574141)) (n := 12)
    (lo := (481319 / 1000000000)) (hi := (12033 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400192574141 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400192574141 / 400000000000) = 1/(100000000000 / 400192574141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14754 : Bounds (1386775679 / 1000000000) (693387841 / 500000000) (Real.log (400192574141 / 100000000000)) := by
  have h := reflection_log_14754_neg
  have he : Real.log (400192574141 / 100000000000) = -Real.log (100000000000 / 400192574141) := by
    rw [show ((400192574141 / 100000000000) : ℝ) = ((100000000000 / 400192574141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14755_neg : (348091981 / 250000000) ≤ -Real.log (500000000000 / 2012184092851) ∧
    -Real.log (500000000000 / 2012184092851) ≤ (1392367927 / 1000000000) := by
  have h := checkLog_sound (w := (12184092851 / 4012184092851)) (n := 12)
    (lo := (1518391 / 250000000)) (hi := (1214713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2012184092851 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2012184092851 / 2000000000000) = 1/(500000000000 / 2012184092851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14755 : Bounds (348091981 / 250000000) (1392367927 / 1000000000) (Real.log (2012184092851 / 500000000000)) := by
  have h := reflection_log_14755_neg
  have he : Real.log (2012184092851 / 500000000000) = -Real.log (500000000000 / 2012184092851) := by
    rw [show ((2012184092851 / 500000000000) : ℝ) = ((500000000000 / 2012184092851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14756_neg : (477245981 / 125000000) ≤ -Real.log (31250000000 / 1422238372093) ∧
    -Real.log (31250000000 / 1422238372093) ≤ (1908983927 / 500000000) := by
  have h := checkLog_sound (w := (422238372093 / 2422238372093)) (n := 12)
    (lo := (88057987 / 250000000)) (hi := (352231949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422238372093 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1422238372093 / 1000000000000) = 1/(31250000000 / 1422238372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14756 : Bounds (477245981 / 125000000) (1908983927 / 500000000) (Real.log (1422238372093 / 31250000000)) := by
  have h := reflection_log_14756_neg
  have he : Real.log (1422238372093 / 31250000000) = -Real.log (31250000000 / 1422238372093) := by
    rw [show ((1422238372093 / 31250000000) : ℝ) = ((31250000000 / 1422238372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14757_neg : (1921004601 / 500000000) ≤ -Real.log (125000000000 / 5827380952381) ∧
    -Real.log (125000000000 / 5827380952381) ≤ (480251151 / 125000000) := by
  have h := checkLog_sound (w := (1827380952381 / 9827380952381)) (n := 12)
    (lo := (188136651 / 500000000)) (hi := (376273303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5827380952381 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5827380952381 / 4000000000000) = 1/(125000000000 / 5827380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14757 : Bounds (1921004601 / 500000000) (480251151 / 125000000) (Real.log (5827380952381 / 125000000000)) := by
  have h := reflection_log_14757_neg
  have he : Real.log (5827380952381 / 125000000000) = -Real.log (125000000000 / 5827380952381) := by
    rw [show ((5827380952381 / 125000000000) : ℝ) = ((125000000000 / 5827380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14758_neg : (336217069 / 500000000) ≤ -Real.log (1000 / 1959) ∧
    -Real.log (1000 / 1959) ≤ (672434139 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 2959)) (n := 12)
    (lo := (336217069 / 500000000)) (hi := (672434139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959 / 1000) = 1/(1000 / 1959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14758 : Bounds (336217069 / 500000000) (672434139 / 1000000000) (Real.log (1959 / 1000)) := by
  have h := reflection_log_14758_neg
  have he : Real.log (1959 / 1000) = -Real.log (1000 / 1959) := by
    rw [show ((1959 / 1000) : ℝ) = ((1000 / 1959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14759_neg : (319418321 / 100000000) ≤ -Real.log (41 / 1000) ∧
    -Real.log (41 / 1000) ≤ (638836643 / 200000000) := by
  have h := checkLog_sound (w := (43 / 207)) (n := 12)
    (lo := (42159449 / 100000000)) (hi := (421594491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 82) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 82) = 1/(41 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14759 : Bounds (-638836643 / 200000000) (-319418321 / 100000000) (Real.log (41 / 1000)) := by
  have h := reflection_log_14759_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14760_neg : (47927 / 50000000) ≤ -Real.log (1000000 / 1000959) ∧
    -Real.log (1000000 / 1000959) ≤ (958541 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 2000959)) (n := 12)
    (lo := (47927 / 50000000)) (hi := (958541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000959 / 1000000) = 1/(1000000 / 1000959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14760 : Bounds (47927 / 50000000) (958541 / 1000000000) (Real.log (1000959 / 1000000)) := by
  have h := reflection_log_14760_neg
  have he : Real.log (1000959 / 1000000) = -Real.log (1000000 / 1000959) := by
    rw [show ((1000959 / 1000000) : ℝ) = ((1000000 / 1000959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14761_neg : (47973 / 50000000) ≤ -Real.log (999041 / 1000000) ∧
    -Real.log (999041 / 1000000) ≤ (959461 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 1999041)) (n := 12)
    (lo := (47973 / 50000000)) (hi := (959461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999041) = 1/(999041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14761 : Bounds (-959461 / 1000000000) (-47973 / 50000000) (Real.log (999041 / 1000000)) := by
  have h := reflection_log_14761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14762_neg : (470805807 / 1000000000) ≤ -Real.log (250000 / 400321) ∧
    -Real.log (250000 / 400321) ≤ (29425363 / 62500000) := by
  have h := checkLog_sound (w := (150321 / 650321)) (n := 12)
    (lo := (470805807 / 1000000000)) (hi := (29425363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400321 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400321 / 250000) = 1/(250000 / 400321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14762 : Bounds (470805807 / 1000000000) (29425363 / 62500000) (Real.log (400321 / 250000)) := by
  have h := reflection_log_14762_neg
  have he : Real.log (400321 / 250000) = -Real.log (250000 / 400321) := by
    rw [show ((400321 / 250000) : ℝ) = ((250000 / 400321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14763_neg : (459752947 / 500000000) ≤ -Real.log (99679 / 250000) ∧
    -Real.log (99679 / 250000) ≤ (114938237 / 125000000) := by
  have h := checkLog_sound (w := (25321 / 224679)) (n := 12)
    (lo := (113179357 / 500000000)) (hi := (45271743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99679) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 99679) = 1/(99679 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14763 : Bounds (-114938237 / 125000000) (-459752947 / 500000000) (Real.log (99679 / 250000)) := by
  have h := reflection_log_14763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14764_neg : (117980759 / 250000000) ≤ -Real.log (500000 / 801537) ∧
    -Real.log (500000 / 801537) ≤ (471923037 / 1000000000) := by
  have h := checkLog_sound (w := (301537 / 1301537)) (n := 12)
    (lo := (117980759 / 250000000)) (hi := (471923037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801537 / 500000) = 1/(500000 / 801537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14764 : Bounds (117980759 / 250000000) (471923037 / 1000000000) (Real.log (801537 / 500000)) := by
  have h := reflection_log_14764_neg
  have he : Real.log (801537 / 500000) = -Real.log (500000 / 801537) := by
    rw [show ((801537 / 500000) : ℝ) = ((500000 / 801537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14765_neg : (924005413 / 1000000000) ≤ -Real.log (198463 / 500000) ∧
    -Real.log (198463 / 500000) ≤ (184801083 / 200000000) := by
  have h := checkLog_sound (w := (51537 / 448463)) (n := 12)
    (lo := (230858233 / 1000000000)) (hi := (115429117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 198463) = 1/(198463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14765 : Bounds (-184801083 / 200000000) (-924005413 / 1000000000) (Real.log (198463 / 500000)) := by
  have h := reflection_log_14765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14766_neg : (452082377 / 1000000000) ≤ -Real.log (159075437631 / 250000000000) ∧
    -Real.log (159075437631 / 250000000000) ≤ (226041189 / 500000000) := by
  have h := checkLog_sound (w := (90924562369 / 409075437631)) (n := 12)
    (lo := (452082377 / 1000000000)) (hi := (226041189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 159075437631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 159075437631) = 1/(159075437631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14766 : Bounds (-226041189 / 500000000) (-452082377 / 1000000000) (Real.log (159075437631 / 250000000000)) := by
  have h := reflection_log_14766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14767_neg : (448700087 / 1000000000) ≤ -Real.log (39903596959 / 62500000000) ∧
    -Real.log (39903596959 / 62500000000) ≤ (56087511 / 125000000) := by
  have h := checkLog_sound (w := (22596403041 / 102403596959)) (n := 12)
    (lo := (448700087 / 1000000000)) (hi := (56087511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 39903596959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 39903596959) = 1/(39903596959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14767 : Bounds (-56087511 / 125000000) (-448700087 / 1000000000) (Real.log (39903596959 / 62500000000)) := by
  have h := reflection_log_14767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14768_neg : (1390311701 / 1000000000) ≤ -Real.log (250000000000 / 1004025421603) ∧
    -Real.log (250000000000 / 1004025421603) ≤ (173788963 / 125000000) := by
  have h := checkLog_sound (w := (4025421603 / 2004025421603)) (n := 12)
    (lo := (4017341 / 1000000000)) (hi := (2008671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1004025421603 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1004025421603 / 1000000000000) = 1/(250000000000 / 1004025421603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14768 : Bounds (1390311701 / 1000000000) (173788963 / 125000000) (Real.log (1004025421603 / 250000000000)) := by
  have h := reflection_log_14768_neg
  have he : Real.log (1004025421603 / 250000000000) = -Real.log (250000000000 / 1004025421603) := by
    rw [show ((1004025421603 / 250000000000) : ℝ) = ((250000000000 / 1004025421603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14769_neg : (10905691 / 7812500) ≤ -Real.log (250000000000 / 1009680645763) ∧
    -Real.log (250000000000 / 1009680645763) ≤ (1395928451 / 1000000000) := by
  have h := checkLog_sound (w := (9680645763 / 2009680645763)) (n := 12)
    (lo := (1204261 / 125000000)) (hi := (9634089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1009680645763 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1009680645763 / 1000000000000) = 1/(250000000000 / 1009680645763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14769 : Bounds (10905691 / 7812500) (1395928451 / 1000000000) (Real.log (1009680645763 / 250000000000)) := by
  have h := reflection_log_14769_neg
  have he : Real.log (1009680645763 / 250000000000) = -Real.log (250000000000 / 1009680645763) := by
    rw [show ((1009680645763 / 250000000000) : ℝ) = ((250000000000 / 1009680645763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14770_neg : (1921004601 / 500000000) ≤ -Real.log (500000000000 / 23309523809523) ∧
    -Real.log (500000000000 / 23309523809523) ≤ (480251151 / 125000000) := by
  have h := checkLog_sound (w := (7309523809523 / 39309523809523)) (n := 12)
    (lo := (188136651 / 500000000)) (hi := (376273303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23309523809523 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23309523809523 / 16000000000000) = 1/(500000000000 / 23309523809523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14770 : Bounds (1921004601 / 500000000) (480251151 / 125000000) (Real.log (23309523809523 / 500000000000)) := by
  have h := reflection_log_14770_neg
  have he : Real.log (23309523809523 / 500000000000) = -Real.log (500000000000 / 23309523809523) := by
    rw [show ((23309523809523 / 500000000000) : ℝ) = ((500000000000 / 23309523809523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14771_neg : (966654337 / 250000000) ≤ -Real.log (12500000000 / 597256097561) ∧
    -Real.log (12500000000 / 597256097561) ≤ (1933308677 / 500000000) := by
  have h := checkLog_sound (w := (197256097561 / 997256097561)) (n := 12)
    (lo := (50110181 / 125000000)) (hi := (400881449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597256097561 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(597256097561 / 400000000000) = 1/(12500000000 / 597256097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14771 : Bounds (966654337 / 250000000) (1933308677 / 500000000) (Real.log (597256097561 / 12500000000)) := by
  have h := reflection_log_14771_neg
  have he : Real.log (597256097561 / 12500000000) = -Real.log (12500000000 / 597256097561) := by
    rw [show ((597256097561 / 12500000000) : ℝ) = ((12500000000 / 597256097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14772_neg : (672944473 / 1000000000) ≤ -Real.log (25 / 49) ∧
    -Real.log (25 / 49) ≤ (336472237 / 500000000) := by
  have h := checkLog_sound (w := (12 / 37)) (n := 12)
    (lo := (672944473 / 1000000000)) (hi := (336472237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 25) = 1/(25 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14772 : Bounds (672944473 / 1000000000) (336472237 / 500000000) (Real.log (49 / 25)) := by
  have h := reflection_log_14772_neg
  have he : Real.log (49 / 25) = -Real.log (25 / 49) := by
    rw [show ((49 / 25) : ℝ) = ((25 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14773_neg : (1609437911 / 500000000) ≤ -Real.log (1 / 25) ∧
    -Real.log (1 / 25) ≤ (3218875827 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 16) = 1/(1 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14773 : Bounds (-3218875827 / 1000000000) (-1609437911 / 500000000) (Real.log (1 / 25)) := by
  have h := reflection_log_14773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14774_neg : (959539 / 1000000000) ≤ -Real.log (3125 / 3128) ∧
    -Real.log (3125 / 3128) ≤ (47977 / 50000000) := by
  have h := checkLog_sound (w := (3 / 6253)) (n := 12)
    (lo := (959539 / 1000000000)) (hi := (47977 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3128 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3128 / 3125) = 1/(3125 / 3128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14774 : Bounds (959539 / 1000000000) (47977 / 50000000) (Real.log (3128 / 3125)) := by
  have h := reflection_log_14774_neg
  have he : Real.log (3128 / 3125) = -Real.log (3125 / 3128) := by
    rw [show ((3128 / 3125) : ℝ) = ((3125 / 3128) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14775_neg : (960461 / 1000000000) ≤ -Real.log (3122 / 3125) ∧
    -Real.log (3122 / 3125) ≤ (480231 / 500000000) := by
  have h := checkLog_sound (w := (3 / 6247)) (n := 12)
    (lo := (960461 / 1000000000)) (hi := (480231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3122) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 3122) = 1/(3122 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14775 : Bounds (-480231 / 500000000) (-960461 / 1000000000) (Real.log (3122 / 3125)) := by
  have h := reflection_log_14775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14776_neg : (235757181 / 500000000) ≤ -Real.log (1000000 / 1602419) ∧
    -Real.log (1000000 / 1602419) ≤ (471514363 / 1000000000) := by
  have h := checkLog_sound (w := (602419 / 2602419)) (n := 12)
    (lo := (235757181 / 500000000)) (hi := (471514363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1602419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1602419 / 1000000) = 1/(1000000 / 1602419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14776 : Bounds (235757181 / 500000000) (471514363 / 1000000000) (Real.log (1602419 / 1000000)) := by
  have h := reflection_log_14776_neg
  have he : Real.log (1602419 / 1000000) = -Real.log (1000000 / 1602419) := by
    rw [show ((1602419 / 1000000) : ℝ) = ((1000000 / 1602419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14777_neg : (922356591 / 1000000000) ≤ -Real.log (397581 / 1000000) ∧
    -Real.log (397581 / 1000000) ≤ (922356593 / 1000000000) := by
  have h := checkLog_sound (w := (102419 / 897581)) (n := 12)
    (lo := (229209411 / 1000000000)) (hi := (57302353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397581) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 397581) = 1/(397581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14777 : Bounds (-922356593 / 1000000000) (-922356591 / 1000000000) (Real.log (397581 / 1000000)) := by
  have h := reflection_log_14777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14778_neg : (23631727 / 50000000) ≤ -Real.log (200000 / 320843) ∧
    -Real.log (200000 / 320843) ≤ (472634541 / 1000000000) := by
  have h := checkLog_sound (w := (120843 / 520843)) (n := 12)
    (lo := (23631727 / 50000000)) (hi := (472634541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320843 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320843 / 200000) = 1/(200000 / 320843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14778 : Bounds (23631727 / 50000000) (472634541 / 1000000000) (Real.log (320843 / 200000)) := by
  have h := reflection_log_14778_neg
  have he : Real.log (320843 / 200000) = -Real.log (200000 / 320843) := by
    rw [show ((320843 / 200000) : ℝ) = ((200000 / 320843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14779_neg : (926884143 / 1000000000) ≤ -Real.log (79157 / 200000) ∧
    -Real.log (79157 / 200000) ≤ (185376829 / 200000000) := by
  have h := checkLog_sound (w := (20843 / 179157)) (n := 12)
    (lo := (233736963 / 1000000000)) (hi := (58434241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 79157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 79157) = 1/(79157 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14779 : Bounds (-185376829 / 200000000) (-926884143 / 1000000000) (Real.log (79157 / 200000)) := by
  have h := reflection_log_14779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14780_neg : (113562401 / 250000000) ≤ -Real.log (25396969351 / 40000000000) ∧
    -Real.log (25396969351 / 40000000000) ≤ (90849921 / 200000000) := by
  have h := checkLog_sound (w := (14603030649 / 65396969351)) (n := 12)
    (lo := (113562401 / 250000000)) (hi := (90849921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 25396969351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 25396969351) = 1/(25396969351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14780 : Bounds (-90849921 / 200000000) (-113562401 / 250000000) (Real.log (25396969351 / 40000000000)) := by
  have h := reflection_log_14780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14781_neg : (450842229 / 1000000000) ≤ -Real.log (637091348439 / 1000000000000) ∧
    -Real.log (637091348439 / 1000000000000) ≤ (45084223 / 100000000) := by
  have h := checkLog_sound (w := (362908651561 / 1637091348439)) (n := 12)
    (lo := (450842229 / 1000000000)) (hi := (45084223 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 637091348439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 637091348439) = 1/(637091348439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14781 : Bounds (-45084223 / 100000000) (-450842229 / 1000000000) (Real.log (637091348439 / 1000000000000)) := by
  have h := reflection_log_14781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14782_neg : (1393870953 / 1000000000) ≤ -Real.log (500000000000 / 2015210736931) ∧
    -Real.log (500000000000 / 2015210736931) ≤ (348467739 / 250000000) := by
  have h := checkLog_sound (w := (15210736931 / 4015210736931)) (n := 12)
    (lo := (7576593 / 1000000000)) (hi := (3788297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2015210736931 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2015210736931 / 2000000000000) = 1/(500000000000 / 2015210736931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14782 : Bounds (1393870953 / 1000000000) (348467739 / 250000000) (Real.log (2015210736931 / 500000000000)) := by
  have h := reflection_log_14782_neg
  have he : Real.log (2015210736931 / 500000000000) = -Real.log (500000000000 / 2015210736931) := by
    rw [show ((2015210736931 / 500000000000) : ℝ) = ((500000000000 / 2015210736931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14783_neg : (1399518683 / 1000000000) ≤ -Real.log (1250000000 / 5066560759) ∧
    -Real.log (1250000000 / 5066560759) ≤ (699759343 / 500000000) := by
  have h := checkLog_sound (w := (66560759 / 10066560759)) (n := 12)
    (lo := (13224323 / 1000000000)) (hi := (3306081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5066560759 / 5000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5066560759 / 5000000000) = 1/(1250000000 / 5066560759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14783 : Bounds (1399518683 / 1000000000) (699759343 / 500000000) (Real.log (5066560759 / 1250000000)) := by
  have h := reflection_log_14783_neg
  have he : Real.log (5066560759 / 1250000000) = -Real.log (1250000000 / 5066560759) := by
    rw [show ((5066560759 / 1250000000) : ℝ) = ((1250000000 / 5066560759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0231 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14784_neg : (966654337 / 250000000) ≤ -Real.log (500000000000 / 23890243902439) ∧
    -Real.log (500000000000 / 23890243902439) ≤ (1933308677 / 500000000) := by
  have h := checkLog_sound (w := (7890243902439 / 39890243902439)) (n := 12)
    (lo := (50110181 / 125000000)) (hi := (400881449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23890243902439 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23890243902439 / 16000000000000) = 1/(500000000000 / 23890243902439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14784 : Bounds (966654337 / 250000000) (1933308677 / 500000000) (Real.log (23890243902439 / 500000000000)) := by
  have h := reflection_log_14784_neg
  have he : Real.log (23890243902439 / 500000000000) = -Real.log (500000000000 / 23890243902439) := by
    rw [show ((23890243902439 / 500000000000) : ℝ) = ((500000000000 / 23890243902439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14785_neg : (778364059 / 200000000) ≤ -Real.log (1 / 49) ∧
    -Real.log (1 / 49) ≤ (3891820301 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 81)) (n := 12)
    (lo := (85216879 / 200000000)) (hi := (106521099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 32) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(49 / 32) = 1/(1 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14785 : Bounds (778364059 / 200000000) (3891820301 / 1000000000) (Real.log (49 / 1)) := by
  have h := reflection_log_14785_neg
  have he : Real.log (49 / 1) = -Real.log (1 / 49) := by
    rw [show ((49 / 1) : ℝ) = ((1 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14786_neg : (673454547 / 1000000000) ≤ -Real.log (1000 / 1961) ∧
    -Real.log (1000 / 1961) ≤ (168363637 / 250000000) := by
  have h := checkLog_sound (w := (961 / 2961)) (n := 12)
    (lo := (673454547 / 1000000000)) (hi := (168363637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961 / 1000) = 1/(1000 / 1961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14786 : Bounds (673454547 / 1000000000) (168363637 / 250000000) (Real.log (1961 / 1000)) := by
  have h := reflection_log_14786_neg
  have he : Real.log (1961 / 1000) = -Real.log (1000 / 1961) := by
    rw [show ((1961 / 1000) : ℝ) = ((1000 / 1961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14787_neg : (324419363 / 100000000) ≤ -Real.log (39 / 1000) ∧
    -Real.log (39 / 1000) ≤ (648838727 / 200000000) := by
  have h := checkLog_sound (w := (47 / 203)) (n := 12)
    (lo := (47160491 / 100000000)) (hi := (471604911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 78) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 78) = 1/(39 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14787 : Bounds (-648838727 / 200000000) (-324419363 / 100000000) (Real.log (39 / 1000)) := by
  have h := reflection_log_14787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14788_neg : (480269 / 500000000) ≤ -Real.log (1000000 / 1000961) ∧
    -Real.log (1000000 / 1000961) ≤ (960539 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 2000961)) (n := 12)
    (lo := (480269 / 500000000)) (hi := (960539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000961 / 1000000) = 1/(1000000 / 1000961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14788 : Bounds (480269 / 500000000) (960539 / 1000000000) (Real.log (1000961 / 1000000)) := by
  have h := reflection_log_14788_neg
  have he : Real.log (1000961 / 1000000) = -Real.log (1000000 / 1000961) := by
    rw [show ((1000961 / 1000000) : ℝ) = ((1000000 / 1000961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14789_neg : (480731 / 500000000) ≤ -Real.log (999039 / 1000000) ∧
    -Real.log (999039 / 1000000) ≤ (961463 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 1999039)) (n := 12)
    (lo := (480731 / 500000000)) (hi := (961463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999039) = 1/(999039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14789 : Bounds (-961463 / 1000000000) (-480731 / 500000000) (Real.log (999039 / 1000000)) := by
  have h := reflection_log_14789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14790_neg : (472226781 / 1000000000) ≤ -Real.log (1000000 / 1603561) ∧
    -Real.log (1000000 / 1603561) ≤ (236113391 / 500000000) := by
  have h := checkLog_sound (w := (603561 / 2603561)) (n := 12)
    (lo := (472226781 / 1000000000)) (hi := (236113391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603561 / 1000000) = 1/(1000000 / 1603561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14790 : Bounds (472226781 / 1000000000) (236113391 / 500000000) (Real.log (1603561 / 1000000)) := by
  have h := reflection_log_14790_neg
  have he : Real.log (1603561 / 1000000) = -Real.log (1000000 / 1603561) := by
    rw [show ((1603561 / 1000000) : ℝ) = ((1000000 / 1603561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14791_neg : (185046619 / 200000000) ≤ -Real.log (396439 / 1000000) ∧
    -Real.log (396439 / 1000000) ≤ (925233097 / 1000000000) := by
  have h := checkLog_sound (w := (103561 / 896439)) (n := 12)
    (lo := (46417183 / 200000000)) (hi := (58021479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 396439) = 1/(396439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14791 : Bounds (-925233097 / 1000000000) (-185046619 / 200000000) (Real.log (396439 / 1000000)) := by
  have h := reflection_log_14791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14792_neg : (118337319 / 250000000) ≤ -Real.log (500000 / 802681) ∧
    -Real.log (500000 / 802681) ≤ (473349277 / 1000000000) := by
  have h := checkLog_sound (w := (302681 / 1302681)) (n := 12)
    (lo := (118337319 / 250000000)) (hi := (473349277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802681 / 500000) = 1/(500000 / 802681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14792 : Bounds (118337319 / 250000000) (473349277 / 1000000000) (Real.log (802681 / 500000)) := by
  have h := reflection_log_14792_neg
  have he : Real.log (802681 / 500000) = -Real.log (500000 / 802681) := by
    rw [show ((802681 / 500000) : ℝ) = ((500000 / 802681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14793_neg : (929786389 / 1000000000) ≤ -Real.log (197319 / 500000) ∧
    -Real.log (197319 / 500000) ≤ (929786391 / 1000000000) := by
  have h := checkLog_sound (w := (52681 / 447319)) (n := 12)
    (lo := (236639209 / 1000000000)) (hi := (23663921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 197319) = 1/(197319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14793 : Bounds (-929786391 / 1000000000) (-929786389 / 1000000000) (Real.log (197319 / 500000)) := by
  have h := reflection_log_14793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14794_neg : (456437113 / 1000000000) ≤ -Real.log (158384212239 / 250000000000) ∧
    -Real.log (158384212239 / 250000000000) ≤ (228218557 / 500000000) := by
  have h := checkLog_sound (w := (91615787761 / 408384212239)) (n := 12)
    (lo := (456437113 / 1000000000)) (hi := (228218557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 158384212239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 158384212239) = 1/(158384212239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14794 : Bounds (-228218557 / 500000000) (-456437113 / 1000000000) (Real.log (158384212239 / 250000000000)) := by
  have h := reflection_log_14794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14795_neg : (226503157 / 500000000) ≤ -Real.log (635714119279 / 1000000000000) ∧
    -Real.log (635714119279 / 1000000000000) ≤ (90601263 / 200000000) := by
  have h := checkLog_sound (w := (364285880721 / 1635714119279)) (n := 12)
    (lo := (226503157 / 500000000)) (hi := (90601263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 635714119279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 635714119279) = 1/(635714119279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14795 : Bounds (-90601263 / 200000000) (-226503157 / 500000000) (Real.log (635714119279 / 1000000000000)) := by
  have h := reflection_log_14795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14796_neg : (11179679 / 8000000) ≤ -Real.log (500000000000 / 2022456166017) ∧
    -Real.log (500000000000 / 2022456166017) ≤ (698729939 / 500000000) := by
  have h := checkLog_sound (w := (22456166017 / 4022456166017)) (n := 12)
    (lo := (2233103 / 200000000)) (hi := (2791379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2022456166017 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2022456166017 / 2000000000000) = 1/(500000000000 / 2022456166017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14796 : Bounds (11179679 / 8000000) (698729939 / 500000000) (Real.log (2022456166017 / 500000000000)) := by
  have h := reflection_log_14796_neg
  have he : Real.log (2022456166017 / 500000000000) = -Real.log (500000000000 / 2022456166017) := by
    rw [show ((2022456166017 / 500000000000) : ℝ) = ((500000000000 / 2022456166017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14797_neg : (280627133 / 200000000) ≤ -Real.log (500000000000 / 2033967838881) ∧
    -Real.log (500000000000 / 2033967838881) ≤ (350783917 / 250000000) := by
  have h := checkLog_sound (w := (33967838881 / 4033967838881)) (n := 12)
    (lo := (3368261 / 200000000)) (hi := (8420653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2033967838881 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2033967838881 / 2000000000000) = 1/(500000000000 / 2033967838881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14797 : Bounds (280627133 / 200000000) (350783917 / 250000000) (Real.log (2033967838881 / 500000000000)) := by
  have h := reflection_log_14797_neg
  have he : Real.log (2033967838881 / 500000000000) = -Real.log (500000000000 / 2033967838881) := by
    rw [show ((2033967838881 / 500000000000) : ℝ) = ((500000000000 / 2033967838881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14798_neg : (3917648177 / 1000000000) ≤ -Real.log (250000000000 / 12570512820513) ∧
    -Real.log (250000000000 / 12570512820513) ≤ (3917648183 / 1000000000) := by
  have h := checkLog_sound (w := (4570512820513 / 20570512820513)) (n := 12)
    (lo := (451912277 / 1000000000)) (hi := (225956139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12570512820513 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12570512820513 / 8000000000000) = 1/(250000000000 / 12570512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14798 : Bounds (3917648177 / 1000000000) (3917648183 / 1000000000) (Real.log (12570512820513 / 250000000000)) := by
  have h := reflection_log_14798_neg
  have he : Real.log (12570512820513 / 250000000000) = -Real.log (250000000000 / 12570512820513) := by
    rw [show ((12570512820513 / 250000000000) : ℝ) = ((250000000000 / 12570512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14799_neg : (673964361 / 1000000000) ≤ -Real.log (500 / 981) ∧
    -Real.log (500 / 981) ≤ (336982181 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1481)) (n := 12)
    (lo := (673964361 / 1000000000)) (hi := (336982181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981 / 500) = 1/(500 / 981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14799 : Bounds (673964361 / 1000000000) (336982181 / 500000000) (Real.log (981 / 500)) := by
  have h := reflection_log_14799_neg
  have he : Real.log (981 / 500) = -Real.log (500 / 981) := by
    rw [show ((981 / 500) : ℝ) = ((500 / 981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14800_neg : (3270169117 / 1000000000) ≤ -Real.log (19 / 500) ∧
    -Real.log (19 / 500) ≤ (1635084561 / 500000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 76) = 1/(19 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14800 : Bounds (-1635084561 / 500000000) (-3270169117 / 1000000000) (Real.log (19 / 500)) := by
  have h := reflection_log_14800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14801_neg : (961537 / 1000000000) ≤ -Real.log (500000 / 500481) ∧
    -Real.log (500000 / 500481) ≤ (480769 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1000481)) (n := 12)
    (lo := (961537 / 1000000000)) (hi := (480769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500481 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500481 / 500000) = 1/(500000 / 500481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14801 : Bounds (961537 / 1000000000) (480769 / 500000000) (Real.log (500481 / 500000)) := by
  have h := reflection_log_14801_neg
  have he : Real.log (500481 / 500000) = -Real.log (500000 / 500481) := by
    rw [show ((500481 / 500000) : ℝ) = ((500000 / 500481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14802_neg : (962463 / 1000000000) ≤ -Real.log (499519 / 500000) ∧
    -Real.log (499519 / 500000) ≤ (30077 / 31250000) := by
  have h := checkLog_sound (w := (481 / 999519)) (n := 12)
    (lo := (962463 / 1000000000)) (hi := (30077 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499519) = 1/(499519 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14802 : Bounds (-30077 / 31250000) (-962463 / 1000000000) (Real.log (499519 / 500000)) := by
  have h := reflection_log_14802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14803_neg : (29558863 / 62500000) ≤ -Real.log (250000 / 401177) ∧
    -Real.log (250000 / 401177) ≤ (472941809 / 1000000000) := by
  have h := checkLog_sound (w := (151177 / 651177)) (n := 12)
    (lo := (29558863 / 62500000)) (hi := (472941809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401177 / 250000) = 1/(250000 / 401177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14803 : Bounds (29558863 / 62500000) (472941809 / 1000000000) (Real.log (401177 / 250000)) := by
  have h := reflection_log_14803_neg
  have he : Real.log (401177 / 250000) = -Real.log (250000 / 401177) := by
    rw [show ((401177 / 250000) : ℝ) = ((250000 / 401177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14804_neg : (464065273 / 500000000) ≤ -Real.log (98823 / 250000) ∧
    -Real.log (98823 / 250000) ≤ (232032637 / 250000000) := by
  have h := checkLog_sound (w := (26177 / 223823)) (n := 12)
    (lo := (117491683 / 500000000)) (hi := (234983367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98823) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 98823) = 1/(98823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14804 : Bounds (-232032637 / 250000000) (-464065273 / 500000000) (Real.log (98823 / 250000)) := by
  have h := reflection_log_14804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14805_neg : (237033307 / 500000000) ≤ -Real.log (500000 / 803257) ∧
    -Real.log (500000 / 803257) ≤ (94813323 / 200000000) := by
  have h := checkLog_sound (w := (303257 / 1303257)) (n := 12)
    (lo := (237033307 / 500000000)) (hi := (94813323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803257 / 500000) = 1/(500000 / 803257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14805 : Bounds (237033307 / 500000000) (94813323 / 200000000) (Real.log (803257 / 500000)) := by
  have h := reflection_log_14805_neg
  have he : Real.log (803257 / 500000) = -Real.log (500000 / 803257) := by
    rw [show ((803257 / 500000) : ℝ) = ((500000 / 803257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14806_neg : (932709789 / 1000000000) ≤ -Real.log (196743 / 500000) ∧
    -Real.log (196743 / 500000) ≤ (932709791 / 1000000000) := by
  have h := checkLog_sound (w := (53257 / 446743)) (n := 12)
    (lo := (239562609 / 1000000000)) (hi := (23956261 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196743) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 196743) = 1/(196743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14806 : Bounds (-932709791 / 1000000000) (-932709789 / 1000000000) (Real.log (196743 / 500000)) := by
  have h := reflection_log_14806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14807_neg : (18345727 / 40000000) ≤ -Real.log (158035191951 / 250000000000) ∧
    -Real.log (158035191951 / 250000000000) ≤ (57330397 / 125000000) := by
  have h := checkLog_sound (w := (91964808049 / 408035191951)) (n := 12)
    (lo := (18345727 / 40000000)) (hi := (57330397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 158035191951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 158035191951) = 1/(158035191951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14807 : Bounds (-57330397 / 125000000) (-18345727 / 40000000) (Real.log (158035191951 / 250000000000)) := by
  have h := reflection_log_14807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14808_neg : (227594369 / 500000000) ≤ -Real.log (39645514671 / 62500000000) ∧
    -Real.log (39645514671 / 62500000000) ≤ (455188739 / 1000000000) := by
  have h := checkLog_sound (w := (22854485329 / 102145514671)) (n := 12)
    (lo := (227594369 / 500000000)) (hi := (455188739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 39645514671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 39645514671) = 1/(39645514671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14808 : Bounds (-455188739 / 1000000000) (-227594369 / 500000000) (Real.log (39645514671 / 62500000000)) := by
  have h := reflection_log_14808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14809_neg : (700536177 / 500000000) ≤ -Real.log (50000000000 / 202977545713) ∧
    -Real.log (50000000000 / 202977545713) ≤ (1401072357 / 1000000000) := by
  have h := checkLog_sound (w := (2977545713 / 402977545713)) (n := 12)
    (lo := (7388997 / 500000000)) (hi := (2955599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202977545713 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(202977545713 / 200000000000) = 1/(50000000000 / 202977545713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14809 : Bounds (700536177 / 500000000) (1401072357 / 1000000000) (Real.log (202977545713 / 50000000000)) := by
  have h := reflection_log_14809_neg
  have he : Real.log (202977545713 / 50000000000) = -Real.log (50000000000 / 202977545713) := by
    rw [show ((202977545713 / 50000000000) : ℝ) = ((50000000000 / 202977545713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14810_neg : (703388201 / 500000000) ≤ -Real.log (62500000000 / 255173309851) ∧
    -Real.log (62500000000 / 255173309851) ≤ (281355281 / 200000000) := by
  have h := checkLog_sound (w := (5173309851 / 505173309851)) (n := 12)
    (lo := (10241021 / 500000000)) (hi := (20482043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255173309851 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(255173309851 / 250000000000) = 1/(62500000000 / 255173309851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14810 : Bounds (703388201 / 500000000) (281355281 / 200000000) (Real.log (255173309851 / 62500000000)) := by
  have h := reflection_log_14810_neg
  have he : Real.log (255173309851 / 62500000000) = -Real.log (62500000000 / 255173309851) := by
    rw [show ((255173309851 / 62500000000) : ℝ) = ((62500000000 / 255173309851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14811_neg : (3917648177 / 1000000000) ≤ -Real.log (20000000000 / 1005641025641) ∧
    -Real.log (20000000000 / 1005641025641) ≤ (3917648183 / 1000000000) := by
  have h := checkLog_sound (w := (365641025641 / 1645641025641)) (n := 12)
    (lo := (451912277 / 1000000000)) (hi := (225956139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1005641025641 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1005641025641 / 640000000000) = 1/(20000000000 / 1005641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14811 : Bounds (3917648177 / 1000000000) (3917648183 / 1000000000) (Real.log (1005641025641 / 20000000000)) := by
  have h := reflection_log_14811_neg
  have he : Real.log (1005641025641 / 20000000000) = -Real.log (20000000000 / 1005641025641) := by
    rw [show ((1005641025641 / 20000000000) : ℝ) = ((20000000000 / 1005641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14812_neg : (3944133477 / 1000000000) ≤ -Real.log (100000000000 / 5163157894737) ∧
    -Real.log (100000000000 / 5163157894737) ≤ (3944133483 / 1000000000) := by
  have h := checkLog_sound (w := (1963157894737 / 8363157894737)) (n := 12)
    (lo := (478397577 / 1000000000)) (hi := (239198789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5163157894737 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5163157894737 / 3200000000000) = 1/(100000000000 / 5163157894737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14812 : Bounds (3944133477 / 1000000000) (3944133483 / 1000000000) (Real.log (5163157894737 / 100000000000)) := by
  have h := reflection_log_14812_neg
  have he : Real.log (5163157894737 / 100000000000) = -Real.log (100000000000 / 5163157894737) := by
    rw [show ((5163157894737 / 100000000000) : ℝ) = ((100000000000 / 5163157894737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14813_neg : (134894783 / 200000000) ≤ -Real.log (1000 / 1963) ∧
    -Real.log (1000 / 1963) ≤ (168618479 / 250000000) := by
  have h := checkLog_sound (w := (963 / 2963)) (n := 12)
    (lo := (134894783 / 200000000)) (hi := (168618479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963 / 1000) = 1/(1000 / 1963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14813 : Bounds (134894783 / 200000000) (168618479 / 250000000) (Real.log (1963 / 1000)) := by
  have h := reflection_log_14813_neg
  have he : Real.log (1963 / 1000) = -Real.log (1000 / 1963) := by
    rw [show ((1963 / 1000) : ℝ) = ((1000 / 1963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14814_neg : (824209341 / 250000000) ≤ -Real.log (37 / 1000) ∧
    -Real.log (37 / 1000) ≤ (3296837369 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 74) = 1/(37 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14814 : Bounds (-3296837369 / 1000000000) (-824209341 / 250000000) (Real.log (37 / 1000)) := by
  have h := reflection_log_14814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14815_neg : (120317 / 125000000) ≤ -Real.log (1000000 / 1000963) ∧
    -Real.log (1000000 / 1000963) ≤ (962537 / 1000000000) := by
  have h := checkLog_sound (w := (963 / 2000963)) (n := 12)
    (lo := (120317 / 125000000)) (hi := (962537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000963 / 1000000) = 1/(1000000 / 1000963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14815 : Bounds (120317 / 125000000) (962537 / 1000000000) (Real.log (1000963 / 1000000)) := by
  have h := reflection_log_14815_neg
  have he : Real.log (1000963 / 1000000) = -Real.log (1000000 / 1000963) := by
    rw [show ((1000963 / 1000000) : ℝ) = ((1000000 / 1000963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14816_neg : (963463 / 1000000000) ≤ -Real.log (999037 / 1000000) ∧
    -Real.log (999037 / 1000000) ≤ (120433 / 125000000) := by
  have h := checkLog_sound (w := (963 / 1999037)) (n := 12)
    (lo := (963463 / 1000000000)) (hi := (120433 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999037) = 1/(999037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14816 : Bounds (-120433 / 125000000) (-963463 / 1000000000) (Real.log (999037 / 1000000)) := by
  have h := reflection_log_14816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14817_neg : (473660061 / 1000000000) ≤ -Real.log (1000000 / 1605861) ∧
    -Real.log (1000000 / 1605861) ≤ (236830031 / 500000000) := by
  have h := checkLog_sound (w := (605861 / 2605861)) (n := 12)
    (lo := (473660061 / 1000000000)) (hi := (236830031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1605861 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1605861 / 1000000) = 1/(1000000 / 1605861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14817 : Bounds (473660061 / 1000000000) (236830031 / 500000000) (Real.log (1605861 / 1000000)) := by
  have h := reflection_log_14817_neg
  have he : Real.log (1605861 / 1000000) = -Real.log (1000000 / 1605861) := by
    rw [show ((1605861 / 1000000) : ℝ) = ((1000000 / 1605861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14818_neg : (931051639 / 1000000000) ≤ -Real.log (394139 / 1000000) ∧
    -Real.log (394139 / 1000000) ≤ (931051641 / 1000000000) := by
  have h := checkLog_sound (w := (105861 / 894139)) (n := 12)
    (lo := (237904459 / 1000000000)) (hi := (11895223 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394139) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 394139) = 1/(394139 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14818 : Bounds (-931051641 / 1000000000) (-931051639 / 1000000000) (Real.log (394139 / 1000000)) := by
  have h := reflection_log_14818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14819_neg : (474787791 / 1000000000) ≤ -Real.log (1000000 / 1607673) ∧
    -Real.log (1000000 / 1607673) ≤ (29674237 / 62500000) := by
  have h := checkLog_sound (w := (607673 / 2607673)) (n := 12)
    (lo := (474787791 / 1000000000)) (hi := (29674237 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1607673 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1607673 / 1000000) = 1/(1000000 / 1607673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14819 : Bounds (474787791 / 1000000000) (29674237 / 62500000) (Real.log (1607673 / 1000000)) := by
  have h := reflection_log_14819_neg
  have he : Real.log (1607673 / 1000000) = -Real.log (1000000 / 1607673) := by
    rw [show ((1607673 / 1000000) : ℝ) = ((1000000 / 1607673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14820_neg : (467829801 / 500000000) ≤ -Real.log (392327 / 1000000) ∧
    -Real.log (392327 / 1000000) ≤ (233914901 / 250000000) := by
  have h := checkLog_sound (w := (107673 / 892327)) (n := 12)
    (lo := (121256211 / 500000000)) (hi := (242512423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392327) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 392327) = 1/(392327 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14820 : Bounds (-233914901 / 250000000) (-467829801 / 500000000) (Real.log (392327 / 1000000)) := by
  have h := reflection_log_14820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14821_neg : (460871811 / 1000000000) ≤ -Real.log (630733525071 / 1000000000000) ∧
    -Real.log (630733525071 / 1000000000000) ≤ (115217953 / 250000000) := by
  have h := checkLog_sound (w := (369266474929 / 1630733525071)) (n := 12)
    (lo := (460871811 / 1000000000)) (hi := (115217953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 630733525071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 630733525071) = 1/(630733525071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14821 : Bounds (-115217953 / 250000000) (-460871811 / 1000000000) (Real.log (630733525071 / 1000000000000)) := by
  have h := reflection_log_14821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14822_neg : (228695789 / 500000000) ≤ -Real.log (632932448679 / 1000000000000) ∧
    -Real.log (632932448679 / 1000000000000) ≤ (457391579 / 1000000000) := by
  have h := checkLog_sound (w := (367067551321 / 1632932448679)) (n := 12)
    (lo := (228695789 / 500000000)) (hi := (457391579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 632932448679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 632932448679) = 1/(632932448679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14822 : Bounds (-457391579 / 1000000000) (-228695789 / 500000000) (Real.log (632932448679 / 1000000000000)) := by
  have h := reflection_log_14822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14823_neg : (14047117 / 10000000) ≤ -Real.log (500000000000 / 2037175970913) ∧
    -Real.log (500000000000 / 2037175970913) ≤ (1404711703 / 1000000000) := by
  have h := checkLog_sound (w := (37175970913 / 4037175970913)) (n := 12)
    (lo := (920867 / 50000000)) (hi := (18417341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2037175970913 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2037175970913 / 2000000000000) = 1/(500000000000 / 2037175970913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14823 : Bounds (14047117 / 10000000) (1404711703 / 1000000000) (Real.log (2037175970913 / 500000000000)) := by
  have h := reflection_log_14823_neg
  have he : Real.log (2037175970913 / 500000000000) = -Real.log (500000000000 / 2037175970913) := by
    rw [show ((2037175970913 / 500000000000) : ℝ) = ((500000000000 / 2037175970913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14824_neg : (705223697 / 500000000) ≤ -Real.log (125000000000 / 512223540567) ∧
    -Real.log (125000000000 / 512223540567) ≤ (1410447397 / 1000000000) := by
  have h := checkLog_sound (w := (12223540567 / 1012223540567)) (n := 12)
    (lo := (12076517 / 500000000)) (hi := (4830607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512223540567 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(512223540567 / 500000000000) = 1/(125000000000 / 512223540567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14824 : Bounds (705223697 / 500000000) (1410447397 / 1000000000) (Real.log (512223540567 / 125000000000)) := by
  have h := reflection_log_14824_neg
  have he : Real.log (512223540567 / 125000000000) = -Real.log (125000000000 / 512223540567) := by
    rw [show ((512223540567 / 125000000000) : ℝ) = ((125000000000 / 512223540567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14825_neg : (3944133477 / 1000000000) ≤ -Real.log (125000000000 / 6453947368421) ∧
    -Real.log (125000000000 / 6453947368421) ≤ (3944133483 / 1000000000) := by
  have h := checkLog_sound (w := (2453947368421 / 10453947368421)) (n := 12)
    (lo := (478397577 / 1000000000)) (hi := (239198789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6453947368421 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6453947368421 / 4000000000000) = 1/(125000000000 / 6453947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14825 : Bounds (3944133477 / 1000000000) (3944133483 / 1000000000) (Real.log (6453947368421 / 125000000000)) := by
  have h := reflection_log_14825_neg
  have he : Real.log (6453947368421 / 125000000000) = -Real.log (125000000000 / 6453947368421) := by
    rw [show ((6453947368421 / 125000000000) : ℝ) = ((125000000000 / 6453947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14826_neg : (1985655639 / 500000000) ≤ -Real.log (125000000000 / 6631756756757) ∧
    -Real.log (125000000000 / 6631756756757) ≤ (992827821 / 250000000) := by
  have h := checkLog_sound (w := (2631756756757 / 10631756756757)) (n := 12)
    (lo := (252787689 / 500000000)) (hi := (505575379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631756756757 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6631756756757 / 4000000000000) = 1/(125000000000 / 6631756756757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14826 : Bounds (1985655639 / 500000000) (992827821 / 250000000) (Real.log (6631756756757 / 125000000000)) := by
  have h := reflection_log_14826_neg
  have he : Real.log (6631756756757 / 125000000000) = -Real.log (125000000000 / 6631756756757) := by
    rw [show ((6631756756757 / 125000000000) : ℝ) = ((125000000000 / 6631756756757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14827_neg : (674983209 / 1000000000) ≤ -Real.log (250 / 491) ∧
    -Real.log (250 / 491) ≤ (67498321 / 100000000) := by
  have h := checkLog_sound (w := (241 / 741)) (n := 12)
    (lo := (674983209 / 1000000000)) (hi := (67498321 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 250) = 1/(250 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14827 : Bounds (674983209 / 1000000000) (67498321 / 100000000) (Real.log (491 / 250)) := by
  have h := reflection_log_14827_neg
  have he : Real.log (491 / 250) = -Real.log (250 / 491) := by
    rw [show ((491 / 250) : ℝ) = ((250 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14828_neg : (1662118169 / 500000000) ≤ -Real.log (9 / 250) ∧
    -Real.log (9 / 250) ≤ (3324236343 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 72) = 1/(9 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14828 : Bounds (-3324236343 / 1000000000) (-1662118169 / 500000000) (Real.log (9 / 250)) := by
  have h := reflection_log_14828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14829_neg : (192707 / 200000000) ≤ -Real.log (250000 / 250241) ∧
    -Real.log (250000 / 250241) ≤ (60221 / 62500000) := by
  have h := checkLog_sound (w := (241 / 500241)) (n := 12)
    (lo := (192707 / 200000000)) (hi := (60221 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250241 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250241 / 250000) = 1/(250000 / 250241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14829 : Bounds (192707 / 200000000) (60221 / 62500000) (Real.log (250241 / 250000)) := by
  have h := reflection_log_14829_neg
  have he : Real.log (250241 / 250000) = -Real.log (250000 / 250241) := by
    rw [show ((250241 / 250000) : ℝ) = ((250000 / 250241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14830_neg : (60279 / 62500000) ≤ -Real.log (249759 / 250000) ∧
    -Real.log (249759 / 250000) ≤ (192893 / 200000000) := by
  have h := checkLog_sound (w := (241 / 499759)) (n := 12)
    (lo := (60279 / 62500000)) (hi := (192893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249759) = 1/(249759 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14830 : Bounds (-192893 / 200000000) (-60279 / 62500000) (Real.log (249759 / 250000)) := by
  have h := reflection_log_14830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14831_neg : (118595383 / 250000000) ≤ -Real.log (50000 / 80351) ∧
    -Real.log (50000 / 80351) ≤ (474381533 / 1000000000) := by
  have h := checkLog_sound (w := (30351 / 130351)) (n := 12)
    (lo := (118595383 / 250000000)) (hi := (474381533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80351 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80351 / 50000) = 1/(50000 / 80351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14831 : Bounds (118595383 / 250000000) (474381533 / 1000000000) (Real.log (80351 / 50000)) := by
  have h := reflection_log_14831_neg
  have he : Real.log (80351 / 50000) = -Real.log (50000 / 80351) := by
    rw [show ((80351 / 50000) : ℝ) = ((50000 / 80351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14832_neg : (466998279 / 500000000) ≤ -Real.log (19649 / 50000) ∧
    -Real.log (19649 / 50000) ≤ (11674957 / 12500000) := by
  have h := checkLog_sound (w := (5351 / 44649)) (n := 12)
    (lo := (120424689 / 500000000)) (hi := (240849379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19649) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 19649) = 1/(19649 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14832 : Bounds (-11674957 / 12500000) (-466998279 / 500000000) (Real.log (19649 / 50000)) := by
  have h := reflection_log_14832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14833_neg : (475512179 / 1000000000) ≤ -Real.log (500000 / 804419) ∧
    -Real.log (500000 / 804419) ≤ (23775609 / 50000000) := by
  have h := checkLog_sound (w := (304419 / 1304419)) (n := 12)
    (lo := (475512179 / 1000000000)) (hi := (23775609 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804419 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804419 / 500000) = 1/(500000 / 804419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14833 : Bounds (475512179 / 1000000000) (23775609 / 50000000) (Real.log (804419 / 500000)) := by
  have h := reflection_log_14833_neg
  have he : Real.log (804419 / 500000) = -Real.log (500000 / 804419) := by
    rw [show ((804419 / 500000) : ℝ) = ((500000 / 804419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14834_neg : (938633481 / 1000000000) ≤ -Real.log (195581 / 500000) ∧
    -Real.log (195581 / 500000) ≤ (938633483 / 1000000000) := by
  have h := checkLog_sound (w := (54419 / 445581)) (n := 12)
    (lo := (245486301 / 1000000000)) (hi := (122743151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195581) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195581) = 1/(195581 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14834 : Bounds (-938633483 / 1000000000) (-938633481 / 1000000000) (Real.log (195581 / 500000)) := by
  have h := reflection_log_14834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14835_neg : (463121303 / 1000000000) ≤ -Real.log (157329072439 / 250000000000) ∧
    -Real.log (157329072439 / 250000000000) ≤ (57890163 / 125000000) := by
  have h := checkLog_sound (w := (92670927561 / 407329072439)) (n := 12)
    (lo := (463121303 / 1000000000)) (hi := (57890163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 157329072439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 157329072439) = 1/(157329072439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14835 : Bounds (-57890163 / 125000000) (-463121303 / 1000000000) (Real.log (157329072439 / 250000000000)) := by
  have h := reflection_log_14835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14836_neg : (229807513 / 500000000) ≤ -Real.log (1578816799 / 2500000000) ∧
    -Real.log (1578816799 / 2500000000) ≤ (459615027 / 1000000000) := by
  have h := checkLog_sound (w := (921183201 / 4078816799)) (n := 12)
    (lo := (229807513 / 500000000)) (hi := (459615027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1578816799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1578816799) = 1/(1578816799 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14836 : Bounds (-459615027 / 1000000000) (-229807513 / 500000000) (Real.log (1578816799 / 2500000000)) := by
  have h := reflection_log_14836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14837_neg : (140837809 / 100000000) ≤ -Real.log (25000000000 / 102232938063) ∧
    -Real.log (25000000000 / 102232938063) ≤ (1408378093 / 1000000000) := by
  have h := checkLog_sound (w := (2232938063 / 202232938063)) (n := 12)
    (lo := (2208373 / 100000000)) (hi := (22083731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102232938063 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(102232938063 / 100000000000) = 1/(25000000000 / 102232938063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14837 : Bounds (140837809 / 100000000) (1408378093 / 1000000000) (Real.log (102232938063 / 25000000000)) := by
  have h := reflection_log_14837_neg
  have he : Real.log (102232938063 / 25000000000) = -Real.log (25000000000 / 102232938063) := by
    rw [show ((102232938063 / 25000000000) : ℝ) = ((25000000000 / 102232938063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14838_neg : (70707283 / 50000000) ≤ -Real.log (125000000000 / 514121387047) ∧
    -Real.log (125000000000 / 514121387047) ≤ (1414145663 / 1000000000) := by
  have h := checkLog_sound (w := (14121387047 / 1014121387047)) (n := 12)
    (lo := (278513 / 10000000)) (hi := (27851301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514121387047 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(514121387047 / 500000000000) = 1/(125000000000 / 514121387047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14838 : Bounds (70707283 / 50000000) (1414145663 / 1000000000) (Real.log (514121387047 / 125000000000)) := by
  have h := reflection_log_14838_neg
  have he : Real.log (514121387047 / 125000000000) = -Real.log (125000000000 / 514121387047) := by
    rw [show ((514121387047 / 125000000000) : ℝ) = ((125000000000 / 514121387047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14839_neg : (1985655639 / 500000000) ≤ -Real.log (500000000000 / 26527027027027) ∧
    -Real.log (500000000000 / 26527027027027) ≤ (992827821 / 250000000) := by
  have h := checkLog_sound (w := (10527027027027 / 42527027027027)) (n := 12)
    (lo := (252787689 / 500000000)) (hi := (505575379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26527027027027 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26527027027027 / 16000000000000) = 1/(500000000000 / 26527027027027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14839 : Bounds (1985655639 / 500000000) (992827821 / 250000000) (Real.log (26527027027027 / 500000000000)) := by
  have h := reflection_log_14839_neg
  have he : Real.log (26527027027027 / 500000000000) = -Real.log (500000000000 / 26527027027027) := by
    rw [show ((26527027027027 / 500000000000) : ℝ) = ((500000000000 / 26527027027027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14840_neg : (3999219547 / 1000000000) ≤ -Real.log (250000000000 / 13638888888889) ∧
    -Real.log (250000000000 / 13638888888889) ≤ (3999219553 / 1000000000) := by
  have h := checkLog_sound (w := (5638888888889 / 21638888888889)) (n := 12)
    (lo := (533483647 / 1000000000)) (hi := (4167841 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13638888888889 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13638888888889 / 8000000000000) = 1/(250000000000 / 13638888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14840 : Bounds (3999219547 / 1000000000) (3999219553 / 1000000000) (Real.log (13638888888889 / 250000000000)) := by
  have h := reflection_log_14840_neg
  have he : Real.log (13638888888889 / 250000000000) = -Real.log (250000000000 / 13638888888889) := by
    rw [show ((13638888888889 / 250000000000) : ℝ) = ((250000000000 / 13638888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14841_neg : (135098449 / 200000000) ≤ -Real.log (200 / 393) ∧
    -Real.log (200 / 393) ≤ (337746123 / 500000000) := by
  have h := checkLog_sound (w := (193 / 593)) (n := 12)
    (lo := (135098449 / 200000000)) (hi := (337746123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 200) = 1/(200 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14841 : Bounds (135098449 / 200000000) (337746123 / 500000000) (Real.log (393 / 200)) := by
  have h := reflection_log_14841_neg
  have he : Real.log (393 / 200) = -Real.log (200 / 393) := by
    rw [show ((393 / 200) : ℝ) = ((200 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14842_neg : (670481443 / 200000000) ≤ -Real.log (7 / 200) ∧
    -Real.log (7 / 200) ≤ (167620361 / 50000000) := by
  have h := checkLog_sound (w := (11 / 39)) (n := 12)
    (lo := (115963699 / 200000000)) (hi := (1132458 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 14) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 14) = 1/(7 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14842 : Bounds (-167620361 / 50000000) (-670481443 / 200000000) (Real.log (7 / 200)) := by
  have h := reflection_log_14842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14843_neg : (482267 / 500000000) ≤ -Real.log (200000 / 200193) ∧
    -Real.log (200000 / 200193) ≤ (192907 / 200000000) := by
  have h := checkLog_sound (w := (193 / 400193)) (n := 12)
    (lo := (482267 / 500000000)) (hi := (192907 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200193 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200193 / 200000) = 1/(200000 / 200193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14843 : Bounds (482267 / 500000000) (192907 / 200000000) (Real.log (200193 / 200000)) := by
  have h := reflection_log_14843_neg
  have he : Real.log (200193 / 200000) = -Real.log (200000 / 200193) := by
    rw [show ((200193 / 200000) : ℝ) = ((200000 / 200193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14844_neg : (193093 / 200000000) ≤ -Real.log (199807 / 200000) ∧
    -Real.log (199807 / 200000) ≤ (482733 / 500000000) := by
  have h := checkLog_sound (w := (193 / 399807)) (n := 12)
    (lo := (193093 / 200000000)) (hi := (482733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199807) = 1/(199807 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14844 : Bounds (-482733 / 500000000) (-193093 / 200000000) (Real.log (199807 / 200000)) := by
  have h := reflection_log_14844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14845_neg : (95021367 / 200000000) ≤ -Real.log (500000 / 804093) ∧
    -Real.log (500000 / 804093) ≤ (118776709 / 250000000) := by
  have h := checkLog_sound (w := (304093 / 1304093)) (n := 12)
    (lo := (95021367 / 200000000)) (hi := (118776709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804093 / 500000) = 1/(500000 / 804093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14845 : Bounds (95021367 / 200000000) (118776709 / 250000000) (Real.log (804093 / 500000)) := by
  have h := reflection_log_14845_neg
  have he : Real.log (804093 / 500000) = -Real.log (500000 / 804093) := by
    rw [show ((804093 / 500000) : ℝ) = ((500000 / 804093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14846_neg : (936968041 / 1000000000) ≤ -Real.log (195907 / 500000) ∧
    -Real.log (195907 / 500000) ≤ (936968043 / 1000000000) := by
  have h := checkLog_sound (w := (54093 / 445907)) (n := 12)
    (lo := (243820861 / 1000000000)) (hi := (121910431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195907) = 1/(195907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14846 : Bounds (-936968043 / 1000000000) (-936968041 / 1000000000) (Real.log (195907 / 500000)) := by
  have h := reflection_log_14846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14847_neg : (476239769 / 1000000000) ≤ -Real.log (1000000 / 1610009) ∧
    -Real.log (1000000 / 1610009) ≤ (47623977 / 100000000) := by
  have h := checkLog_sound (w := (610009 / 2610009)) (n := 12)
    (lo := (476239769 / 1000000000)) (hi := (47623977 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1610009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1610009 / 1000000) = 1/(1000000 / 1610009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14847 : Bounds (476239769 / 1000000000) (47623977 / 100000000) (Real.log (1610009 / 1000000)) := by
  have h := reflection_log_14847_neg
  have he : Real.log (1610009 / 1000000) = -Real.log (1000000 / 1610009) := by
    rw [show ((1610009 / 1000000) : ℝ) = ((1000000 / 1610009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


