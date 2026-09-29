-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0181__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0181__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:34:35.434227+00:00
-- url     : https://prove2.me/theorems/5ed5a9f9-a520-436d-a8c6-d3961148eb8e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0181 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0182, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0181 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0182, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0183)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0181 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0182, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0183)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0181 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0182, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0183) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0181 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0182, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0183).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0181 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11584_neg : (50718931 / 1000000000) ≤ -Real.log (950545801311 / 1000000000000) ∧
    -Real.log (950545801311 / 1000000000000) ≤ (12679733 / 250000000) := by
  have h := checkLog_sound (w := (49454198689 / 1950545801311)) (n := 12)
    (lo := (50718931 / 1000000000)) (hi := (12679733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 950545801311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 950545801311) = 1/(950545801311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11584 : Bounds (-12679733 / 250000000) (-50718931 / 1000000000) (Real.log (950545801311 / 1000000000000)) := by
  have h := reflection_log_11584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11585_neg : (113080849 / 250000000) ≤ -Real.log (20000000000 / 31439204647) ∧
    -Real.log (20000000000 / 31439204647) ≤ (452323397 / 1000000000) := by
  have h := checkLog_sound (w := (11439204647 / 51439204647)) (n := 12)
    (lo := (113080849 / 250000000)) (hi := (452323397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31439204647 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31439204647 / 20000000000) = 1/(20000000000 / 31439204647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11585 : Bounds (113080849 / 250000000) (452323397 / 1000000000) (Real.log (31439204647 / 20000000000)) := by
  have h := reflection_log_11585_neg
  have he : Real.log (31439204647 / 20000000000) = -Real.log (20000000000 / 31439204647) := by
    rw [show ((31439204647 / 20000000000) : ℝ) = ((20000000000 / 31439204647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11586_neg : (454366897 / 1000000000) ≤ -Real.log (100000000000 / 157517582013) ∧
    -Real.log (100000000000 / 157517582013) ≤ (227183449 / 500000000) := by
  have h := checkLog_sound (w := (57517582013 / 257517582013)) (n := 12)
    (lo := (454366897 / 1000000000)) (hi := (227183449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157517582013 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157517582013 / 100000000000) = 1/(100000000000 / 157517582013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11586 : Bounds (454366897 / 1000000000) (227183449 / 500000000) (Real.log (157517582013 / 100000000000)) := by
  have h := reflection_log_11586_neg
  have he : Real.log (157517582013 / 100000000000) = -Real.log (100000000000 / 157517582013) := by
    rw [show ((157517582013 / 100000000000) : ℝ) = ((100000000000 / 157517582013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11587_neg : (919793361 / 1000000000) ≤ -Real.log (31250000000 / 78399122807) ∧
    -Real.log (31250000000 / 78399122807) ≤ (919793363 / 1000000000) := by
  have h := checkLog_sound (w := (15899122807 / 140899122807)) (n := 12)
    (lo := (226646181 / 1000000000)) (hi := (113323091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78399122807 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(78399122807 / 62500000000) = 1/(31250000000 / 78399122807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11587 : Bounds (919793361 / 1000000000) (919793363 / 1000000000) (Real.log (78399122807 / 31250000000)) := by
  have h := reflection_log_11587_neg
  have he : Real.log (78399122807 / 31250000000) = -Real.log (31250000000 / 78399122807) := by
    rw [show ((78399122807 / 31250000000) : ℝ) = ((31250000000 / 78399122807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11588_neg : (115281043 / 125000000) ≤ -Real.log (500000000000 / 1257469244289) ∧
    -Real.log (500000000000 / 1257469244289) ≤ (461124173 / 500000000) := by
  have h := checkLog_sound (w := (257469244289 / 2257469244289)) (n := 12)
    (lo := (57275291 / 250000000)) (hi := (45820233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257469244289 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1257469244289 / 1000000000000) = 1/(500000000000 / 1257469244289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11588 : Bounds (115281043 / 125000000) (461124173 / 500000000) (Real.log (1257469244289 / 500000000000)) := by
  have h := reflection_log_11588_neg
  have he : Real.log (1257469244289 / 500000000000) = -Real.log (500000000000 / 1257469244289) := by
    rw [show ((1257469244289 / 500000000000) : ℝ) = ((500000000000 / 1257469244289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11589_neg : (89768017 / 250000000) ≤ -Real.log (125 / 179) ∧
    -Real.log (125 / 179) ≤ (359072069 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 152)) (n := 12)
    (lo := (89768017 / 250000000)) (hi := (359072069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179 / 125) = 1/(125 / 179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11589 : Bounds (89768017 / 250000000) (359072069 / 1000000000) (Real.log (179 / 125)) := by
  have h := reflection_log_11589_neg
  have he : Real.log (179 / 125) = -Real.log (125 / 179) := by
    rw [show ((179 / 125) : ℝ) = ((125 / 179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11590_neg : (28281693 / 50000000) ≤ -Real.log (71 / 125) ∧
    -Real.log (71 / 125) ≤ (565633861 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 98)) (n := 12)
    (lo := (28281693 / 50000000)) (hi := (565633861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 71) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 71) = 1/(71 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11590 : Bounds (-565633861 / 1000000000) (-28281693 / 50000000) (Real.log (71 / 125)) := by
  have h := reflection_log_11590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11591_neg : (215953 / 500000000) ≤ -Real.log (62500 / 62527) ∧
    -Real.log (62500 / 62527) ≤ (431907 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 125027)) (n := 12)
    (lo := (215953 / 500000000)) (hi := (431907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62527 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62527 / 62500) = 1/(62500 / 62527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11591 : Bounds (215953 / 500000000) (431907 / 1000000000) (Real.log (62527 / 62500)) := by
  have h := reflection_log_11591_neg
  have he : Real.log (62527 / 62500) = -Real.log (62500 / 62527) := by
    rw [show ((62527 / 62500) : ℝ) = ((62500 / 62527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11592_neg : (432093 / 1000000000) ≤ -Real.log (62473 / 62500) ∧
    -Real.log (62473 / 62500) ≤ (216047 / 500000000) := by
  have h := checkLog_sound (w := (27 / 124973)) (n := 12)
    (lo := (432093 / 1000000000)) (hi := (216047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62473) = 1/(62473 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11592 : Bounds (-216047 / 500000000) (-432093 / 1000000000) (Real.log (62473 / 62500)) := by
  have h := reflection_log_11592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11593_neg : (1257851 / 6250000) ≤ -Real.log (500000 / 611469) ∧
    -Real.log (500000 / 611469) ≤ (201256161 / 1000000000) := by
  have h := checkLog_sound (w := (111469 / 1111469)) (n := 12)
    (lo := (1257851 / 6250000)) (hi := (201256161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611469 / 500000) = 1/(500000 / 611469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11593 : Bounds (1257851 / 6250000) (201256161 / 1000000000) (Real.log (611469 / 500000)) := by
  have h := reflection_log_11593_neg
  have he : Real.log (611469 / 500000) = -Real.log (500000 / 611469) := by
    rw [show ((611469 / 500000) : ℝ) = ((500000 / 611469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11594_neg : (252235137 / 1000000000) ≤ -Real.log (388531 / 500000) ∧
    -Real.log (388531 / 500000) ≤ (126117569 / 500000000) := by
  have h := checkLog_sound (w := (111469 / 888531)) (n := 12)
    (lo := (252235137 / 1000000000)) (hi := (126117569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388531) = 1/(388531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11594 : Bounds (-126117569 / 500000000) (-252235137 / 1000000000) (Real.log (388531 / 500000)) := by
  have h := reflection_log_11594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11595_neg : (202050651 / 1000000000) ≤ -Real.log (100000 / 122391) ∧
    -Real.log (100000 / 122391) ≤ (50512663 / 250000000) := by
  have h := checkLog_sound (w := (22391 / 222391)) (n := 12)
    (lo := (202050651 / 1000000000)) (hi := (50512663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122391 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122391 / 100000) = 1/(100000 / 122391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11595 : Bounds (202050651 / 1000000000) (50512663 / 250000000) (Real.log (122391 / 100000)) := by
  have h := reflection_log_11595_neg
  have he : Real.log (122391 / 100000) = -Real.log (100000 / 122391) := by
    rw [show ((122391 / 100000) : ℝ) = ((100000 / 122391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11596_neg : (126743393 / 500000000) ≤ -Real.log (77609 / 100000) ∧
    -Real.log (77609 / 100000) ≤ (253486787 / 1000000000) := by
  have h := checkLog_sound (w := (22391 / 177609)) (n := 12)
    (lo := (126743393 / 500000000)) (hi := (253486787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77609) = 1/(77609 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11596 : Bounds (-253486787 / 1000000000) (-126743393 / 500000000) (Real.log (77609 / 100000)) := by
  have h := reflection_log_11596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11597_neg : (25718067 / 500000000) ≤ -Real.log (9498643119 / 10000000000) ∧
    -Real.log (9498643119 / 10000000000) ≤ (10287227 / 200000000) := by
  have h := checkLog_sound (w := (501356881 / 19498643119)) (n := 12)
    (lo := (25718067 / 500000000)) (hi := (10287227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9498643119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9498643119) = 1/(9498643119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11597 : Bounds (-10287227 / 200000000) (-25718067 / 500000000) (Real.log (9498643119 / 10000000000)) := by
  have h := reflection_log_11597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11598_neg : (50978977 / 1000000000) ≤ -Real.log (237574662039 / 250000000000) ∧
    -Real.log (237574662039 / 250000000000) ≤ (25489489 / 500000000) := by
  have h := checkLog_sound (w := (12425337961 / 487574662039)) (n := 12)
    (lo := (50978977 / 1000000000)) (hi := (25489489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237574662039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237574662039) = 1/(237574662039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11598 : Bounds (-25489489 / 500000000) (-50978977 / 1000000000) (Real.log (237574662039 / 250000000000)) := by
  have h := reflection_log_11598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11599_neg : (226745649 / 500000000) ≤ -Real.log (500000000000 / 786898600111) ∧
    -Real.log (500000000000 / 786898600111) ≤ (453491299 / 1000000000) := by
  have h := checkLog_sound (w := (286898600111 / 1286898600111)) (n := 12)
    (lo := (226745649 / 500000000)) (hi := (453491299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786898600111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786898600111 / 500000000000) = 1/(500000000000 / 786898600111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11599 : Bounds (226745649 / 500000000) (453491299 / 1000000000) (Real.log (786898600111 / 500000000000)) := by
  have h := reflection_log_11599_neg
  have he : Real.log (786898600111 / 500000000000) = -Real.log (500000000000 / 786898600111) := by
    rw [show ((786898600111 / 500000000000) : ℝ) = ((500000000000 / 786898600111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11600_neg : (227768719 / 500000000) ≤ -Real.log (500000000000 / 788510353181) ∧
    -Real.log (500000000000 / 788510353181) ≤ (455537439 / 1000000000) := by
  have h := checkLog_sound (w := (288510353181 / 1288510353181)) (n := 12)
    (lo := (227768719 / 500000000)) (hi := (455537439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((788510353181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(788510353181 / 500000000000) = 1/(500000000000 / 788510353181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11600 : Bounds (227768719 / 500000000) (455537439 / 1000000000) (Real.log (788510353181 / 500000000000)) := by
  have h := reflection_log_11600_neg
  have he : Real.log (788510353181 / 500000000000) = -Real.log (500000000000 / 788510353181) := by
    rw [show ((788510353181 / 500000000000) : ℝ) = ((500000000000 / 788510353181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11601_neg : (115281043 / 125000000) ≤ -Real.log (3906250000 / 9823978471) ∧
    -Real.log (3906250000 / 9823978471) ≤ (461124173 / 500000000) := by
  have h := checkLog_sound (w := (2011478471 / 17636478471)) (n := 12)
    (lo := (57275291 / 250000000)) (hi := (45820233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9823978471 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9823978471 / 7812500000) = 1/(3906250000 / 9823978471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11601 : Bounds (115281043 / 125000000) (461124173 / 500000000) (Real.log (9823978471 / 3906250000)) := by
  have h := reflection_log_11601_neg
  have he : Real.log (9823978471 / 3906250000) = -Real.log (3906250000 / 9823978471) := by
    rw [show ((9823978471 / 3906250000) : ℝ) = ((3906250000 / 9823978471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11602_neg : (115588241 / 125000000) ≤ -Real.log (250000000000 / 630281690141) ∧
    -Real.log (250000000000 / 630281690141) ≤ (92470593 / 100000000) := by
  have h := checkLog_sound (w := (130281690141 / 1130281690141)) (n := 12)
    (lo := (57889687 / 250000000)) (hi := (231558749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630281690141 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(630281690141 / 500000000000) = 1/(250000000000 / 630281690141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11602 : Bounds (115588241 / 125000000) (92470593 / 100000000) (Real.log (630281690141 / 250000000000)) := by
  have h := reflection_log_11602_neg
  have he : Real.log (630281690141 / 250000000000) = -Real.log (250000000000 / 630281690141) := by
    rw [show ((630281690141 / 250000000000) : ℝ) = ((250000000000 / 630281690141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11603_neg : (89942537 / 250000000) ≤ -Real.log (1000 / 1433) ∧
    -Real.log (1000 / 1433) ≤ (359770149 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2433)) (n := 12)
    (lo := (89942537 / 250000000)) (hi := (359770149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433 / 1000) = 1/(1000 / 1433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11603 : Bounds (89942537 / 250000000) (359770149 / 1000000000) (Real.log (1433 / 1000)) := by
  have h := reflection_log_11603_neg
  have he : Real.log (1433 / 1000) = -Real.log (1000 / 1433) := by
    rw [show ((1433 / 1000) : ℝ) = ((1000 / 1433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11604_neg : (22695839 / 40000000) ≤ -Real.log (567 / 1000) ∧
    -Real.log (567 / 1000) ≤ (70924497 / 125000000) := by
  have h := checkLog_sound (w := (433 / 1567)) (n := 12)
    (lo := (22695839 / 40000000)) (hi := (70924497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 567) = 1/(567 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11604 : Bounds (-70924497 / 125000000) (-22695839 / 40000000) (Real.log (567 / 1000)) := by
  have h := reflection_log_11604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11605_neg : (216453 / 500000000) ≤ -Real.log (1000000 / 1000433) ∧
    -Real.log (1000000 / 1000433) ≤ (432907 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2000433)) (n := 12)
    (lo := (216453 / 500000000)) (hi := (432907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000433 / 1000000) = 1/(1000000 / 1000433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11605 : Bounds (216453 / 500000000) (432907 / 1000000000) (Real.log (1000433 / 1000000)) := by
  have h := reflection_log_11605_neg
  have he : Real.log (1000433 / 1000000) = -Real.log (1000000 / 1000433) := by
    rw [show ((1000433 / 1000000) : ℝ) = ((1000000 / 1000433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11606_neg : (433093 / 1000000000) ≤ -Real.log (999567 / 1000000) ∧
    -Real.log (999567 / 1000000) ≤ (216547 / 500000000) := by
  have h := checkLog_sound (w := (433 / 1999567)) (n := 12)
    (lo := (433093 / 1000000000)) (hi := (216547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999567) = 1/(999567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11606 : Bounds (-216547 / 500000000) (-433093 / 1000000000) (Real.log (999567 / 1000000)) := by
  have h := reflection_log_11606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11607_neg : (100854941 / 500000000) ≤ -Real.log (1000000 / 1223493) ∧
    -Real.log (1000000 / 1223493) ≤ (201709883 / 1000000000) := by
  have h := checkLog_sound (w := (223493 / 2223493)) (n := 12)
    (lo := (100854941 / 500000000)) (hi := (201709883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223493 / 1000000) = 1/(1000000 / 1223493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11607 : Bounds (100854941 / 500000000) (201709883 / 1000000000) (Real.log (1223493 / 1000000)) := by
  have h := reflection_log_11607_neg
  have he : Real.log (1223493 / 1000000) = -Real.log (1000000 / 1223493) := by
    rw [show ((1223493 / 1000000) : ℝ) = ((1000000 / 1223493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11608_neg : (252949621 / 1000000000) ≤ -Real.log (776507 / 1000000) ∧
    -Real.log (776507 / 1000000) ≤ (126474811 / 500000000) := by
  have h := checkLog_sound (w := (223493 / 1776507)) (n := 12)
    (lo := (252949621 / 1000000000)) (hi := (126474811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776507) = 1/(776507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11608 : Bounds (-126474811 / 500000000) (-252949621 / 1000000000) (Real.log (776507 / 1000000)) := by
  have h := reflection_log_11608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11609_neg : (20250483 / 100000000) ≤ -Real.log (500000 / 612233) ∧
    -Real.log (500000 / 612233) ≤ (202504831 / 1000000000) := by
  have h := checkLog_sound (w := (112233 / 1112233)) (n := 12)
    (lo := (20250483 / 100000000)) (hi := (202504831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612233 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612233 / 500000) = 1/(500000 / 612233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11609 : Bounds (20250483 / 100000000) (202504831 / 1000000000) (Real.log (612233 / 500000)) := by
  have h := reflection_log_11609_neg
  have he : Real.log (612233 / 500000) = -Real.log (500000 / 612233) := by
    rw [show ((612233 / 500000) : ℝ) = ((500000 / 612233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11610_neg : (127101727 / 500000000) ≤ -Real.log (387767 / 500000) ∧
    -Real.log (387767 / 500000) ≤ (50840691 / 200000000) := by
  have h := checkLog_sound (w := (112233 / 887767)) (n := 12)
    (lo := (127101727 / 500000000)) (hi := (50840691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387767) = 1/(387767 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11610 : Bounds (-50840691 / 200000000) (-127101727 / 500000000) (Real.log (387767 / 500000)) := by
  have h := reflection_log_11610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11611_neg : (807791 / 15625000) ≤ -Real.log (237403753711 / 250000000000) ∧
    -Real.log (237403753711 / 250000000000) ≤ (413589 / 8000000) := by
  have h := checkLog_sound (w := (12596246289 / 487403753711)) (n := 12)
    (lo := (807791 / 15625000)) (hi := (413589 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237403753711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237403753711) = 1/(237403753711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11611 : Bounds (-413589 / 8000000) (-807791 / 15625000) (Real.log (237403753711 / 250000000000)) := by
  have h := reflection_log_11611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11612_neg : (51239739 / 1000000000) ≤ -Real.log (950050878951 / 1000000000000) ∧
    -Real.log (950050878951 / 1000000000000) ≤ (2561987 / 50000000) := by
  have h := checkLog_sound (w := (49949121049 / 1950050878951)) (n := 12)
    (lo := (51239739 / 1000000000)) (hi := (2561987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 950050878951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 950050878951) = 1/(950050878951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11612 : Bounds (-2561987 / 50000000) (-51239739 / 1000000000) (Real.log (950050878951 / 1000000000000)) := by
  have h := reflection_log_11612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11613_neg : (28416219 / 62500000) ≤ -Real.log (500000000 / 787818397) ∧
    -Real.log (500000000 / 787818397) ≤ (90931901 / 200000000) := by
  have h := checkLog_sound (w := (287818397 / 1287818397)) (n := 12)
    (lo := (28416219 / 62500000)) (hi := (90931901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787818397 / 500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787818397 / 500000000) = 1/(500000000 / 787818397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11613 : Bounds (28416219 / 62500000) (90931901 / 200000000) (Real.log (787818397 / 500000000)) := by
  have h := reflection_log_11613_neg
  have he : Real.log (787818397 / 500000000) = -Real.log (500000000 / 787818397) := by
    rw [show ((787818397 / 500000000) : ℝ) = ((500000000 / 787818397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11614_neg : (91341657 / 200000000) ≤ -Real.log (500000000000 / 789434118943) ∧
    -Real.log (500000000000 / 789434118943) ≤ (228354143 / 500000000) := by
  have h := checkLog_sound (w := (289434118943 / 1289434118943)) (n := 12)
    (lo := (91341657 / 200000000)) (hi := (228354143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789434118943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789434118943 / 500000000000) = 1/(500000000000 / 789434118943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11614 : Bounds (91341657 / 200000000) (228354143 / 500000000) (Real.log (789434118943 / 500000000000)) := by
  have h := reflection_log_11614_neg
  have he : Real.log (789434118943 / 500000000000) = -Real.log (500000000000 / 789434118943) := by
    rw [show ((789434118943 / 500000000000) : ℝ) = ((500000000000 / 789434118943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11615_neg : (115588241 / 125000000) ≤ -Real.log (500000000000 / 1260563380281) ∧
    -Real.log (500000000000 / 1260563380281) ≤ (92470593 / 100000000) := by
  have h := checkLog_sound (w := (260563380281 / 2260563380281)) (n := 12)
    (lo := (57889687 / 250000000)) (hi := (231558749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260563380281 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1260563380281 / 1000000000000) = 1/(500000000000 / 1260563380281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11615 : Bounds (115588241 / 125000000) (92470593 / 100000000) (Real.log (1260563380281 / 500000000000)) := by
  have h := reflection_log_11615_neg
  have he : Real.log (1260563380281 / 500000000000) = -Real.log (500000000000 / 1260563380281) := by
    rw [show ((1260563380281 / 500000000000) : ℝ) = ((500000000000 / 1260563380281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11616_neg : (927166123 / 1000000000) ≤ -Real.log (976562500 / 2468102403) ∧
    -Real.log (976562500 / 2468102403) ≤ (7417329 / 8000000) := by
  have h := checkLog_sound (w := (514977403 / 4421227403)) (n := 12)
    (lo := (234018943 / 1000000000)) (hi := (1828273 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2468102403 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2468102403 / 1953125000) = 1/(976562500 / 2468102403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11616 : Bounds (927166123 / 1000000000) (7417329 / 8000000) (Real.log (2468102403 / 976562500)) := by
  have h := reflection_log_11616_neg
  have he : Real.log (2468102403 / 976562500) = -Real.log (976562500 / 2468102403) := by
    rw [show ((2468102403 / 976562500) : ℝ) = ((976562500 / 2468102403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11617_neg : (180233871 / 500000000) ≤ -Real.log (500 / 717) ∧
    -Real.log (500 / 717) ≤ (360467743 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1217)) (n := 12)
    (lo := (180233871 / 500000000)) (hi := (360467743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717 / 500) = 1/(500 / 717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11617 : Bounds (180233871 / 500000000) (360467743 / 1000000000) (Real.log (717 / 500)) := by
  have h := reflection_log_11617_neg
  have he : Real.log (717 / 500) = -Real.log (500 / 717) := by
    rw [show ((717 / 500) : ℝ) = ((500 / 717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11618_neg : (1422903 / 2500000) ≤ -Real.log (283 / 500) ∧
    -Real.log (283 / 500) ≤ (569161201 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 783)) (n := 12)
    (lo := (1422903 / 2500000)) (hi := (569161201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 283) = 1/(283 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11618 : Bounds (-569161201 / 1000000000) (-1422903 / 2500000) (Real.log (283 / 500)) := by
  have h := reflection_log_11618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11619_neg : (86781 / 200000000) ≤ -Real.log (500000 / 500217) ∧
    -Real.log (500000 / 500217) ≤ (216953 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1000217)) (n := 12)
    (lo := (86781 / 200000000)) (hi := (216953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500217 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500217 / 500000) = 1/(500000 / 500217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11619 : Bounds (86781 / 200000000) (216953 / 500000000) (Real.log (500217 / 500000)) := by
  have h := reflection_log_11619_neg
  have he : Real.log (500217 / 500000) = -Real.log (500000 / 500217) := by
    rw [show ((500217 / 500000) : ℝ) = ((500000 / 500217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11620_neg : (217047 / 500000000) ≤ -Real.log (499783 / 500000) ∧
    -Real.log (499783 / 500000) ≤ (86819 / 200000000) := by
  have h := checkLog_sound (w := (217 / 999783)) (n := 12)
    (lo := (217047 / 500000000)) (hi := (86819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499783) = 1/(499783 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11620 : Bounds (-86819 / 200000000) (-217047 / 500000000) (Real.log (499783 / 500000)) := by
  have h := reflection_log_11620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11621_neg : (202163399 / 1000000000) ≤ -Real.log (62500 / 76503) ∧
    -Real.log (62500 / 76503) ≤ (1010817 / 5000000) := by
  have h := checkLog_sound (w := (14003 / 139003)) (n := 12)
    (lo := (202163399 / 1000000000)) (hi := (1010817 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76503 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76503 / 62500) = 1/(62500 / 76503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11621 : Bounds (202163399 / 1000000000) (1010817 / 5000000) (Real.log (76503 / 62500)) := by
  have h := reflection_log_11621_neg
  have he : Real.log (76503 / 62500) = -Real.log (62500 / 76503) := by
    rw [show ((76503 / 62500) : ℝ) = ((62500 / 76503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11622_neg : (31708077 / 125000000) ≤ -Real.log (48497 / 62500) ∧
    -Real.log (48497 / 62500) ≤ (253664617 / 1000000000) := by
  have h := checkLog_sound (w := (14003 / 110997)) (n := 12)
    (lo := (31708077 / 125000000)) (hi := (253664617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48497) = 1/(48497 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11622 : Bounds (-253664617 / 1000000000) (-31708077 / 125000000) (Real.log (48497 / 62500)) := by
  have h := reflection_log_11622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11623_neg : (202958803 / 1000000000) ≤ -Real.log (500000 / 612511) ∧
    -Real.log (500000 / 612511) ≤ (50739701 / 250000000) := by
  have h := checkLog_sound (w := (112511 / 1112511)) (n := 12)
    (lo := (202958803 / 1000000000)) (hi := (50739701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612511 / 500000) = 1/(500000 / 612511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11623 : Bounds (202958803 / 1000000000) (50739701 / 250000000) (Real.log (612511 / 500000)) := by
  have h := reflection_log_11623_neg
  have he : Real.log (612511 / 500000) = -Real.log (500000 / 612511) := by
    rw [show ((612511 / 500000) : ℝ) = ((500000 / 612511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11624_neg : (254920637 / 1000000000) ≤ -Real.log (387489 / 500000) ∧
    -Real.log (387489 / 500000) ≤ (127460319 / 500000000) := by
  have h := checkLog_sound (w := (112511 / 887489)) (n := 12)
    (lo := (254920637 / 1000000000)) (hi := (127460319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387489) = 1/(387489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11624 : Bounds (-127460319 / 500000000) (-254920637 / 1000000000) (Real.log (387489 / 500000)) := by
  have h := reflection_log_11624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11625_neg : (25980917 / 500000000) ≤ -Real.log (237341274879 / 250000000000) ∧
    -Real.log (237341274879 / 250000000000) ≤ (10392367 / 200000000) := by
  have h := checkLog_sound (w := (12658725121 / 487341274879)) (n := 12)
    (lo := (25980917 / 500000000)) (hi := (10392367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237341274879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237341274879) = 1/(237341274879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11625 : Bounds (-10392367 / 200000000) (-25980917 / 500000000) (Real.log (237341274879 / 250000000000)) := by
  have h := reflection_log_11625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11626_neg : (51501217 / 1000000000) ≤ -Real.log (3710165991 / 3906250000) ∧
    -Real.log (3710165991 / 3906250000) ≤ (25750609 / 500000000) := by
  have h := checkLog_sound (w := (196084009 / 7616415991)) (n := 12)
    (lo := (51501217 / 1000000000)) (hi := (25750609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3710165991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3710165991) = 1/(3710165991 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11626 : Bounds (-25750609 / 500000000) (-51501217 / 1000000000) (Real.log (3710165991 / 3906250000)) := by
  have h := reflection_log_11626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11627_neg : (91165603 / 200000000) ≤ -Real.log (25000000000 / 39436975483) ∧
    -Real.log (25000000000 / 39436975483) ≤ (28489251 / 62500000) := by
  have h := checkLog_sound (w := (14436975483 / 64436975483)) (n := 12)
    (lo := (91165603 / 200000000)) (hi := (28489251 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39436975483 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39436975483 / 25000000000) = 1/(25000000000 / 39436975483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11627 : Bounds (91165603 / 200000000) (28489251 / 62500000) (Real.log (39436975483 / 25000000000)) := by
  have h := reflection_log_11627_neg
  have he : Real.log (39436975483 / 25000000000) = -Real.log (25000000000 / 39436975483) := by
    rw [show ((39436975483 / 25000000000) : ℝ) = ((25000000000 / 39436975483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11628_neg : (5723493 / 12500000) ≤ -Real.log (500000000000 / 790359210197) ∧
    -Real.log (500000000000 / 790359210197) ≤ (457879441 / 1000000000) := by
  have h := checkLog_sound (w := (290359210197 / 1290359210197)) (n := 12)
    (lo := (5723493 / 12500000)) (hi := (457879441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790359210197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790359210197 / 500000000000) = 1/(500000000000 / 790359210197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11628 : Bounds (5723493 / 12500000) (457879441 / 1000000000) (Real.log (790359210197 / 500000000000)) := by
  have h := reflection_log_11628_neg
  have he : Real.log (790359210197 / 500000000000) = -Real.log (500000000000 / 790359210197) := by
    rw [show ((790359210197 / 500000000000) : ℝ) = ((500000000000 / 790359210197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11629_neg : (927166123 / 1000000000) ≤ -Real.log (100000000000 / 252733686067) ∧
    -Real.log (100000000000 / 252733686067) ≤ (7417329 / 8000000) := by
  have h := checkLog_sound (w := (52733686067 / 452733686067)) (n := 12)
    (lo := (234018943 / 1000000000)) (hi := (1828273 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252733686067 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(252733686067 / 200000000000) = 1/(100000000000 / 252733686067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11629 : Bounds (927166123 / 1000000000) (7417329 / 8000000) (Real.log (252733686067 / 100000000000)) := by
  have h := reflection_log_11629_neg
  have he : Real.log (252733686067 / 100000000000) = -Real.log (100000000000 / 252733686067) := by
    rw [show ((252733686067 / 100000000000) : ℝ) = ((100000000000 / 252733686067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11630_neg : (464814471 / 500000000) ≤ -Real.log (500000000000 / 1266784452297) ∧
    -Real.log (500000000000 / 1266784452297) ≤ (58101809 / 62500000) := by
  have h := checkLog_sound (w := (266784452297 / 2266784452297)) (n := 12)
    (lo := (118240881 / 500000000)) (hi := (236481763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266784452297 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1266784452297 / 1000000000000) = 1/(500000000000 / 1266784452297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11630 : Bounds (464814471 / 500000000) (58101809 / 62500000) (Real.log (1266784452297 / 500000000000)) := by
  have h := reflection_log_11630_neg
  have he : Real.log (1266784452297 / 500000000000) = -Real.log (500000000000 / 1266784452297) := by
    rw [show ((1266784452297 / 500000000000) : ℝ) = ((500000000000 / 1266784452297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11631_neg : (361164849 / 1000000000) ≤ -Real.log (200 / 287) ∧
    -Real.log (200 / 287) ≤ (7223297 / 20000000) := by
  have h := checkLog_sound (w := (87 / 487)) (n := 12)
    (lo := (361164849 / 1000000000)) (hi := (7223297 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 200) = 1/(200 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11631 : Bounds (361164849 / 1000000000) (7223297 / 20000000) (Real.log (287 / 200)) := by
  have h := reflection_log_11631_neg
  have he : Real.log (287 / 200) = -Real.log (200 / 287) := by
    rw [show ((287 / 200) : ℝ) = ((200 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11632_neg : (570929547 / 1000000000) ≤ -Real.log (113 / 200) ∧
    -Real.log (113 / 200) ≤ (142732387 / 250000000) := by
  have h := checkLog_sound (w := (87 / 313)) (n := 12)
    (lo := (570929547 / 1000000000)) (hi := (142732387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 113) = 1/(113 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11632 : Bounds (-142732387 / 250000000) (-570929547 / 1000000000) (Real.log (113 / 200)) := by
  have h := reflection_log_11632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11633_neg : (86981 / 200000000) ≤ -Real.log (200000 / 200087) ∧
    -Real.log (200000 / 200087) ≤ (217453 / 500000000) := by
  have h := checkLog_sound (w := (87 / 400087)) (n := 12)
    (lo := (86981 / 200000000)) (hi := (217453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200087 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200087 / 200000) = 1/(200000 / 200087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11633 : Bounds (86981 / 200000000) (217453 / 500000000) (Real.log (200087 / 200000)) := by
  have h := reflection_log_11633_neg
  have he : Real.log (200087 / 200000) = -Real.log (200000 / 200087) := by
    rw [show ((200087 / 200000) : ℝ) = ((200000 / 200087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11634_neg : (217547 / 500000000) ≤ -Real.log (199913 / 200000) ∧
    -Real.log (199913 / 200000) ≤ (87019 / 200000000) := by
  have h := checkLog_sound (w := (87 / 399913)) (n := 12)
    (lo := (217547 / 500000000)) (hi := (87019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199913) = 1/(199913 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11634 : Bounds (-87019 / 200000000) (-217547 / 500000000) (Real.log (199913 / 200000)) := by
  have h := reflection_log_11634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11635_neg : (101308763 / 500000000) ≤ -Real.log (250000 / 306151) ∧
    -Real.log (250000 / 306151) ≤ (202617527 / 1000000000) := by
  have h := checkLog_sound (w := (56151 / 556151)) (n := 12)
    (lo := (101308763 / 500000000)) (hi := (202617527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306151 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306151 / 250000) = 1/(250000 / 306151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11635 : Bounds (101308763 / 500000000) (202617527 / 1000000000) (Real.log (306151 / 250000)) := by
  have h := reflection_log_11635_neg
  have he : Real.log (306151 / 250000) = -Real.log (250000 / 306151) := by
    rw [show ((306151 / 250000) : ℝ) = ((250000 / 306151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11636_neg : (63595353 / 250000000) ≤ -Real.log (193849 / 250000) ∧
    -Real.log (193849 / 250000) ≤ (254381413 / 1000000000) := by
  have h := checkLog_sound (w := (56151 / 443849)) (n := 12)
    (lo := (63595353 / 250000000)) (hi := (254381413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193849) = 1/(193849 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11636 : Bounds (-254381413 / 1000000000) (-63595353 / 250000000) (Real.log (193849 / 250000)) := by
  have h := reflection_log_11636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11637_neg : (40682677 / 200000000) ≤ -Real.log (1000000 / 1225579) ∧
    -Real.log (1000000 / 1225579) ≤ (101706693 / 500000000) := by
  have h := checkLog_sound (w := (225579 / 2225579)) (n := 12)
    (lo := (40682677 / 200000000)) (hi := (101706693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225579 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225579 / 1000000) = 1/(1000000 / 1225579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11637 : Bounds (40682677 / 200000000) (101706693 / 500000000) (Real.log (1225579 / 1000000)) := by
  have h := reflection_log_11637_neg
  have he : Real.log (1225579 / 1000000) = -Real.log (1000000 / 1225579) := by
    rw [show ((1225579 / 1000000) : ℝ) = ((1000000 / 1225579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11638_neg : (2045117 / 8000000) ≤ -Real.log (774421 / 1000000) ∧
    -Real.log (774421 / 1000000) ≤ (127819813 / 500000000) := by
  have h := checkLog_sound (w := (225579 / 1774421)) (n := 12)
    (lo := (2045117 / 8000000)) (hi := (127819813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774421) = 1/(774421 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11638 : Bounds (-127819813 / 500000000) (-2045117 / 8000000) (Real.log (774421 / 1000000)) := by
  have h := reflection_log_11638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11639_neg : (163207 / 3125000) ≤ -Real.log (949114114759 / 1000000000000) ∧
    -Real.log (949114114759 / 1000000000000) ≤ (52226241 / 1000000000) := by
  have h := checkLog_sound (w := (50885885241 / 1949114114759)) (n := 12)
    (lo := (163207 / 3125000)) (hi := (52226241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 949114114759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 949114114759) = 1/(949114114759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11639 : Bounds (-52226241 / 1000000000) (-163207 / 3125000) (Real.log (949114114759 / 1000000000000)) := by
  have h := reflection_log_11639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11640_neg : (10352777 / 200000000) ≤ -Real.log (59347065199 / 62500000000) ∧
    -Real.log (59347065199 / 62500000000) ≤ (25881943 / 500000000) := by
  have h := checkLog_sound (w := (3152934801 / 121847065199)) (n := 12)
    (lo := (10352777 / 200000000)) (hi := (25881943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59347065199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59347065199) = 1/(59347065199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11640 : Bounds (-25881943 / 500000000) (-10352777 / 200000000) (Real.log (59347065199 / 62500000000)) := by
  have h := reflection_log_11640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11641_neg : (228499469 / 500000000) ≤ -Real.log (100000000000 / 157932720829) ∧
    -Real.log (100000000000 / 157932720829) ≤ (456998939 / 1000000000) := by
  have h := checkLog_sound (w := (57932720829 / 257932720829)) (n := 12)
    (lo := (228499469 / 500000000)) (hi := (456998939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157932720829 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157932720829 / 100000000000) = 1/(100000000000 / 157932720829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11641 : Bounds (228499469 / 500000000) (456998939 / 1000000000) (Real.log (157932720829 / 100000000000)) := by
  have h := reflection_log_11641_neg
  have he : Real.log (157932720829 / 100000000000) = -Real.log (100000000000 / 157932720829) := by
    rw [show ((157932720829 / 100000000000) : ℝ) = ((100000000000 / 157932720829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11642_neg : (459053011 / 1000000000) ≤ -Real.log (25000000000 / 39564364861) ∧
    -Real.log (25000000000 / 39564364861) ≤ (114763253 / 250000000) := by
  have h := checkLog_sound (w := (14564364861 / 64564364861)) (n := 12)
    (lo := (459053011 / 1000000000)) (hi := (114763253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39564364861 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39564364861 / 25000000000) = 1/(25000000000 / 39564364861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11642 : Bounds (459053011 / 1000000000) (114763253 / 250000000) (Real.log (39564364861 / 25000000000)) := by
  have h := reflection_log_11642_neg
  have he : Real.log (39564364861 / 25000000000) = -Real.log (25000000000 / 39564364861) := by
    rw [show ((39564364861 / 25000000000) : ℝ) = ((25000000000 / 39564364861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11643_neg : (464814471 / 500000000) ≤ -Real.log (62500000000 / 158348056537) ∧
    -Real.log (62500000000 / 158348056537) ≤ (58101809 / 62500000) := by
  have h := checkLog_sound (w := (33348056537 / 283348056537)) (n := 12)
    (lo := (118240881 / 500000000)) (hi := (236481763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158348056537 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158348056537 / 125000000000) = 1/(62500000000 / 158348056537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11643 : Bounds (464814471 / 500000000) (58101809 / 62500000) (Real.log (158348056537 / 62500000000)) := by
  have h := reflection_log_11643_neg
  have he : Real.log (158348056537 / 62500000000) = -Real.log (62500000000 / 158348056537) := by
    rw [show ((158348056537 / 62500000000) : ℝ) = ((62500000000 / 158348056537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11644_neg : (233023599 / 250000000) ≤ -Real.log (20000000000 / 50796460177) ∧
    -Real.log (20000000000 / 50796460177) ≤ (466047199 / 500000000) := by
  have h := checkLog_sound (w := (10796460177 / 90796460177)) (n := 12)
    (lo := (14934201 / 62500000)) (hi := (238947217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50796460177 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50796460177 / 40000000000) = 1/(20000000000 / 50796460177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11644 : Bounds (233023599 / 250000000) (466047199 / 500000000) (Real.log (50796460177 / 20000000000)) := by
  have h := reflection_log_11644_neg
  have he : Real.log (50796460177 / 20000000000) = -Real.log (20000000000 / 50796460177) := by
    rw [show ((50796460177 / 20000000000) : ℝ) = ((20000000000 / 50796460177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11645_neg : (36186147 / 100000000) ≤ -Real.log (250 / 359) ∧
    -Real.log (250 / 359) ≤ (361861471 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 609)) (n := 12)
    (lo := (36186147 / 100000000)) (hi := (361861471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359 / 250) = 1/(250 / 359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11645 : Bounds (36186147 / 100000000) (361861471 / 1000000000) (Real.log (359 / 250)) := by
  have h := reflection_log_11645_neg
  have he : Real.log (359 / 250) = -Real.log (250 / 359) := by
    rw [show ((359 / 250) : ℝ) = ((250 / 359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11646_neg : (572701027 / 1000000000) ≤ -Real.log (141 / 250) ∧
    -Real.log (141 / 250) ≤ (143175257 / 250000000) := by
  have h := checkLog_sound (w := (109 / 391)) (n := 12)
    (lo := (572701027 / 1000000000)) (hi := (143175257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 141) = 1/(141 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11646 : Bounds (-143175257 / 250000000) (-572701027 / 1000000000) (Real.log (141 / 250)) := by
  have h := reflection_log_11646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11647_neg : (6811 / 15625000) ≤ -Real.log (250000 / 250109) ∧
    -Real.log (250000 / 250109) ≤ (87181 / 200000000) := by
  have h := checkLog_sound (w := (109 / 500109)) (n := 12)
    (lo := (6811 / 15625000)) (hi := (87181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250109 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250109 / 250000) = 1/(250000 / 250109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11647 : Bounds (6811 / 15625000) (87181 / 200000000) (Real.log (250109 / 250000)) := by
  have h := reflection_log_11647_neg
  have he : Real.log (250109 / 250000) = -Real.log (250000 / 250109) := by
    rw [show ((250109 / 250000) : ℝ) = ((250000 / 250109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0182 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11648_neg : (87219 / 200000000) ≤ -Real.log (249891 / 250000) ∧
    -Real.log (249891 / 250000) ≤ (3407 / 7812500) := by
  have h := checkLog_sound (w := (109 / 499891)) (n := 12)
    (lo := (87219 / 200000000)) (hi := (3407 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249891) = 1/(249891 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11648 : Bounds (-3407 / 7812500) (-87219 / 200000000) (Real.log (249891 / 250000)) := by
  have h := reflection_log_11648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11649_neg : (203071447 / 1000000000) ≤ -Real.log (25000 / 30629) ∧
    -Real.log (25000 / 30629) ≤ (25383931 / 125000000) := by
  have h := checkLog_sound (w := (5629 / 55629)) (n := 12)
    (lo := (203071447 / 1000000000)) (hi := (25383931 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30629 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30629 / 25000) = 1/(25000 / 30629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11649 : Bounds (203071447 / 1000000000) (25383931 / 125000000) (Real.log (30629 / 25000)) := by
  have h := reflection_log_11649_neg
  have he : Real.log (30629 / 25000) = -Real.log (25000 / 30629) := by
    rw [show ((30629 / 25000) : ℝ) = ((25000 / 30629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11650_neg : (127549361 / 500000000) ≤ -Real.log (19371 / 25000) ∧
    -Real.log (19371 / 25000) ≤ (255098723 / 1000000000) := by
  have h := checkLog_sound (w := (5629 / 44371)) (n := 12)
    (lo := (127549361 / 500000000)) (hi := (255098723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19371) = 1/(19371 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11650 : Bounds (-255098723 / 1000000000) (-127549361 / 500000000) (Real.log (19371 / 25000)) := by
  have h := reflection_log_11650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11651_neg : (203867761 / 1000000000) ≤ -Real.log (125000 / 153267) ∧
    -Real.log (125000 / 153267) ≤ (101933881 / 500000000) := by
  have h := checkLog_sound (w := (28267 / 278267)) (n := 12)
    (lo := (203867761 / 1000000000)) (hi := (101933881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153267 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153267 / 125000) = 1/(125000 / 153267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11651 : Bounds (203867761 / 1000000000) (101933881 / 500000000) (Real.log (153267 / 125000)) := by
  have h := reflection_log_11651_neg
  have he : Real.log (153267 / 125000) = -Real.log (125000 / 153267) := by
    rw [show ((153267 / 125000) : ℝ) = ((125000 / 153267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11652_neg : (256359131 / 1000000000) ≤ -Real.log (96733 / 125000) ∧
    -Real.log (96733 / 125000) ≤ (64089783 / 250000000) := by
  have h := checkLog_sound (w := (28267 / 221733)) (n := 12)
    (lo := (256359131 / 1000000000)) (hi := (64089783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96733) = 1/(96733 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11652 : Bounds (-64089783 / 250000000) (-256359131 / 1000000000) (Real.log (96733 / 125000)) := by
  have h := reflection_log_11652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11653_neg : (5249137 / 100000000) ≤ -Real.log (14825976711 / 15625000000) ∧
    -Real.log (14825976711 / 15625000000) ≤ (52491371 / 1000000000) := by
  have h := checkLog_sound (w := (799023289 / 30450976711)) (n := 12)
    (lo := (5249137 / 100000000)) (hi := (52491371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14825976711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14825976711) = 1/(14825976711 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11653 : Bounds (-52491371 / 1000000000) (-5249137 / 100000000) (Real.log (14825976711 / 15625000000)) := by
  have h := reflection_log_11653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11654_neg : (26013637 / 500000000) ≤ -Real.log (593314359 / 625000000) ∧
    -Real.log (593314359 / 625000000) ≤ (2081091 / 40000000) := by
  have h := checkLog_sound (w := (31685641 / 1218314359)) (n := 12)
    (lo := (26013637 / 500000000)) (hi := (2081091 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 593314359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 593314359) = 1/(593314359 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11654 : Bounds (-2081091 / 40000000) (-26013637 / 500000000) (Real.log (593314359 / 625000000)) := by
  have h := reflection_log_11654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11655_neg : (45817017 / 100000000) ≤ -Real.log (50000000000 / 79058902483) ∧
    -Real.log (50000000000 / 79058902483) ≤ (458170171 / 1000000000) := by
  have h := checkLog_sound (w := (29058902483 / 129058902483)) (n := 12)
    (lo := (45817017 / 100000000)) (hi := (458170171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79058902483 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79058902483 / 50000000000) = 1/(50000000000 / 79058902483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11655 : Bounds (45817017 / 100000000) (458170171 / 1000000000) (Real.log (79058902483 / 50000000000)) := by
  have h := reflection_log_11655_neg
  have he : Real.log (79058902483 / 50000000000) = -Real.log (50000000000 / 79058902483) := by
    rw [show ((79058902483 / 50000000000) : ℝ) = ((50000000000 / 79058902483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11656_neg : (115056723 / 250000000) ≤ -Real.log (500000000000 / 792216720251) ∧
    -Real.log (500000000000 / 792216720251) ≤ (460226893 / 1000000000) := by
  have h := checkLog_sound (w := (292216720251 / 1292216720251)) (n := 12)
    (lo := (115056723 / 250000000)) (hi := (460226893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792216720251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792216720251 / 500000000000) = 1/(500000000000 / 792216720251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11656 : Bounds (115056723 / 250000000) (460226893 / 1000000000) (Real.log (792216720251 / 500000000000)) := by
  have h := reflection_log_11656_neg
  have he : Real.log (792216720251 / 500000000000) = -Real.log (500000000000 / 792216720251) := by
    rw [show ((792216720251 / 500000000000) : ℝ) = ((500000000000 / 792216720251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11657_neg : (233023599 / 250000000) ≤ -Real.log (62500000000 / 158738938053) ∧
    -Real.log (62500000000 / 158738938053) ≤ (466047199 / 500000000) := by
  have h := checkLog_sound (w := (33738938053 / 283738938053)) (n := 12)
    (lo := (14934201 / 62500000)) (hi := (238947217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158738938053 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158738938053 / 125000000000) = 1/(62500000000 / 158738938053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11657 : Bounds (233023599 / 250000000) (466047199 / 500000000) (Real.log (158738938053 / 62500000000)) := by
  have h := reflection_log_11657_neg
  have he : Real.log (158738938053 / 62500000000) = -Real.log (62500000000 / 158738938053) := by
    rw [show ((158738938053 / 62500000000) : ℝ) = ((62500000000 / 158738938053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11658_neg : (934562497 / 1000000000) ≤ -Real.log (500000000000 / 1273049645391) ∧
    -Real.log (500000000000 / 1273049645391) ≤ (934562499 / 1000000000) := by
  have h := checkLog_sound (w := (273049645391 / 2273049645391)) (n := 12)
    (lo := (241415317 / 1000000000)) (hi := (120707659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273049645391 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1273049645391 / 1000000000000) = 1/(500000000000 / 1273049645391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11658 : Bounds (934562497 / 1000000000) (934562499 / 1000000000) (Real.log (1273049645391 / 500000000000)) := by
  have h := reflection_log_11658_neg
  have he : Real.log (1273049645391 / 500000000000) = -Real.log (500000000000 / 1273049645391) := by
    rw [show ((1273049645391 / 500000000000) : ℝ) = ((500000000000 / 1273049645391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11659_neg : (362557607 / 1000000000) ≤ -Real.log (1000 / 1437) ∧
    -Real.log (1000 / 1437) ≤ (45319701 / 125000000) := by
  have h := checkLog_sound (w := (437 / 2437)) (n := 12)
    (lo := (362557607 / 1000000000)) (hi := (45319701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1437 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1437 / 1000) = 1/(1000 / 1437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11659 : Bounds (362557607 / 1000000000) (45319701 / 125000000) (Real.log (1437 / 1000)) := by
  have h := reflection_log_11659_neg
  have he : Real.log (1437 / 1000) = -Real.log (1000 / 1437) := by
    rw [show ((1437 / 1000) : ℝ) = ((1000 / 1437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11660_neg : (11489513 / 20000000) ≤ -Real.log (563 / 1000) ∧
    -Real.log (563 / 1000) ≤ (574475651 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 1563)) (n := 12)
    (lo := (11489513 / 20000000)) (hi := (574475651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 563) = 1/(563 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11660 : Bounds (-574475651 / 1000000000) (-11489513 / 20000000) (Real.log (563 / 1000)) := by
  have h := reflection_log_11660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11661_neg : (54613 / 125000000) ≤ -Real.log (1000000 / 1000437) ∧
    -Real.log (1000000 / 1000437) ≤ (87381 / 200000000) := by
  have h := checkLog_sound (w := (437 / 2000437)) (n := 12)
    (lo := (54613 / 125000000)) (hi := (87381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000437 / 1000000) = 1/(1000000 / 1000437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11661 : Bounds (54613 / 125000000) (87381 / 200000000) (Real.log (1000437 / 1000000)) := by
  have h := reflection_log_11661_neg
  have he : Real.log (1000437 / 1000000) = -Real.log (1000000 / 1000437) := by
    rw [show ((1000437 / 1000000) : ℝ) = ((1000000 / 1000437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11662_neg : (87419 / 200000000) ≤ -Real.log (999563 / 1000000) ∧
    -Real.log (999563 / 1000000) ≤ (54637 / 125000000) := by
  have h := checkLog_sound (w := (437 / 1999563)) (n := 12)
    (lo := (87419 / 200000000)) (hi := (54637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999563) = 1/(999563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11662 : Bounds (-54637 / 125000000) (-87419 / 200000000) (Real.log (999563 / 1000000)) := by
  have h := reflection_log_11662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11663_neg : (203525163 / 1000000000) ≤ -Real.log (250000 / 306429) ∧
    -Real.log (250000 / 306429) ≤ (50881291 / 250000000) := by
  have h := checkLog_sound (w := (56429 / 556429)) (n := 12)
    (lo := (203525163 / 1000000000)) (hi := (50881291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306429 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306429 / 250000) = 1/(250000 / 306429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11663 : Bounds (203525163 / 1000000000) (50881291 / 250000000) (Real.log (306429 / 250000)) := by
  have h := reflection_log_11663_neg
  have he : Real.log (306429 / 250000) = -Real.log (250000 / 306429) := by
    rw [show ((306429 / 250000) : ℝ) = ((250000 / 306429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11664_neg : (255816547 / 1000000000) ≤ -Real.log (193571 / 250000) ∧
    -Real.log (193571 / 250000) ≤ (63954137 / 250000000) := by
  have h := checkLog_sound (w := (56429 / 443571)) (n := 12)
    (lo := (255816547 / 1000000000)) (hi := (63954137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193571) = 1/(193571 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11664 : Bounds (-63954137 / 250000000) (-255816547 / 1000000000) (Real.log (193571 / 250000)) := by
  have h := reflection_log_11664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11665_neg : (40864549 / 200000000) ≤ -Real.log (500000 / 613347) ∧
    -Real.log (500000 / 613347) ≤ (102161373 / 500000000) := by
  have h := checkLog_sound (w := (113347 / 1113347)) (n := 12)
    (lo := (40864549 / 200000000)) (hi := (102161373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613347 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613347 / 500000) = 1/(500000 / 613347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11665 : Bounds (40864549 / 200000000) (102161373 / 500000000) (Real.log (613347 / 500000)) := by
  have h := reflection_log_11665_neg
  have he : Real.log (613347 / 500000) = -Real.log (500000 / 613347) := by
    rw [show ((613347 / 500000) : ℝ) = ((500000 / 613347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11666_neg : (2008441 / 7812500) ≤ -Real.log (386653 / 500000) ∧
    -Real.log (386653 / 500000) ≤ (257080449 / 1000000000) := by
  have h := checkLog_sound (w := (113347 / 886653)) (n := 12)
    (lo := (2008441 / 7812500)) (hi := (257080449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386653) = 1/(386653 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11666 : Bounds (-257080449 / 1000000000) (-2008441 / 7812500) (Real.log (386653 / 500000)) := by
  have h := reflection_log_11666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11667_neg : (26378851 / 500000000) ≤ -Real.log (237152457591 / 250000000000) ∧
    -Real.log (237152457591 / 250000000000) ≤ (52757703 / 1000000000) := by
  have h := checkLog_sound (w := (12847542409 / 487152457591)) (n := 12)
    (lo := (26378851 / 500000000)) (hi := (52757703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237152457591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237152457591) = 1/(237152457591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11667 : Bounds (-52757703 / 1000000000) (-26378851 / 500000000) (Real.log (237152457591 / 250000000000)) := by
  have h := reflection_log_11667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11668_neg : (6536423 / 125000000) ≤ -Real.log (59315767959 / 62500000000) ∧
    -Real.log (59315767959 / 62500000000) ≤ (10458277 / 200000000) := by
  have h := checkLog_sound (w := (3184232041 / 121815767959)) (n := 12)
    (lo := (6536423 / 125000000)) (hi := (10458277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59315767959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59315767959) = 1/(59315767959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11668 : Bounds (-10458277 / 200000000) (-6536423 / 125000000) (Real.log (59315767959 / 62500000000)) := by
  have h := reflection_log_11668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11669_neg : (45934171 / 100000000) ≤ -Real.log (500000000000 / 791515774573) ∧
    -Real.log (500000000000 / 791515774573) ≤ (459341711 / 1000000000) := by
  have h := checkLog_sound (w := (291515774573 / 1291515774573)) (n := 12)
    (lo := (45934171 / 100000000)) (hi := (459341711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791515774573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791515774573 / 500000000000) = 1/(500000000000 / 791515774573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11669 : Bounds (45934171 / 100000000) (459341711 / 1000000000) (Real.log (791515774573 / 500000000000)) := by
  have h := reflection_log_11669_neg
  have he : Real.log (791515774573 / 500000000000) = -Real.log (500000000000 / 791515774573) := by
    rw [show ((791515774573 / 500000000000) : ℝ) = ((500000000000 / 791515774573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11670_neg : (230701597 / 500000000) ≤ -Real.log (50000000000 / 79314915441) ∧
    -Real.log (50000000000 / 79314915441) ≤ (92280639 / 200000000) := by
  have h := checkLog_sound (w := (29314915441 / 129314915441)) (n := 12)
    (lo := (230701597 / 500000000)) (hi := (92280639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79314915441 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79314915441 / 50000000000) = 1/(50000000000 / 79314915441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11670 : Bounds (230701597 / 500000000) (92280639 / 200000000) (Real.log (79314915441 / 50000000000)) := by
  have h := reflection_log_11670_neg
  have he : Real.log (79314915441 / 50000000000) = -Real.log (50000000000 / 79314915441) := by
    rw [show ((79314915441 / 50000000000) : ℝ) = ((50000000000 / 79314915441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11671_neg : (934562497 / 1000000000) ≤ -Real.log (50000000000 / 127304964539) ∧
    -Real.log (50000000000 / 127304964539) ≤ (934562499 / 1000000000) := by
  have h := checkLog_sound (w := (27304964539 / 227304964539)) (n := 12)
    (lo := (241415317 / 1000000000)) (hi := (120707659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127304964539 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127304964539 / 100000000000) = 1/(50000000000 / 127304964539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11671 : Bounds (934562497 / 1000000000) (934562499 / 1000000000) (Real.log (127304964539 / 50000000000)) := by
  have h := reflection_log_11671_neg
  have he : Real.log (127304964539 / 50000000000) = -Real.log (50000000000 / 127304964539) := by
    rw [show ((127304964539 / 50000000000) : ℝ) = ((50000000000 / 127304964539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11672_neg : (937033257 / 1000000000) ≤ -Real.log (500000000000 / 1276198934281) ∧
    -Real.log (500000000000 / 1276198934281) ≤ (937033259 / 1000000000) := by
  have h := checkLog_sound (w := (276198934281 / 2276198934281)) (n := 12)
    (lo := (243886077 / 1000000000)) (hi := (121943039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276198934281 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1276198934281 / 1000000000000) = 1/(500000000000 / 1276198934281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11672 : Bounds (937033257 / 1000000000) (937033259 / 1000000000) (Real.log (1276198934281 / 500000000000)) := by
  have h := reflection_log_11672_neg
  have he : Real.log (1276198934281 / 500000000000) = -Real.log (500000000000 / 1276198934281) := by
    rw [show ((1276198934281 / 500000000000) : ℝ) = ((500000000000 / 1276198934281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11673_neg : (363253259 / 1000000000) ≤ -Real.log (500 / 719) ∧
    -Real.log (500 / 719) ≤ (18162663 / 50000000) := by
  have h := checkLog_sound (w := (219 / 1219)) (n := 12)
    (lo := (363253259 / 1000000000)) (hi := (18162663 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719 / 500) = 1/(500 / 719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11673 : Bounds (363253259 / 1000000000) (18162663 / 50000000) (Real.log (719 / 500)) := by
  have h := reflection_log_11673_neg
  have he : Real.log (719 / 500) = -Real.log (500 / 719) := by
    rw [show ((719 / 500) : ℝ) = ((500 / 719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11674_neg : (576253429 / 1000000000) ≤ -Real.log (281 / 500) ∧
    -Real.log (281 / 500) ≤ (57625343 / 100000000) := by
  have h := checkLog_sound (w := (219 / 781)) (n := 12)
    (lo := (576253429 / 1000000000)) (hi := (57625343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 281) = 1/(281 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11674 : Bounds (-57625343 / 100000000) (-576253429 / 1000000000) (Real.log (281 / 500)) := by
  have h := reflection_log_11674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11675_neg : (27369 / 62500000) ≤ -Real.log (500000 / 500219) ∧
    -Real.log (500000 / 500219) ≤ (87581 / 200000000) := by
  have h := checkLog_sound (w := (219 / 1000219)) (n := 12)
    (lo := (27369 / 62500000)) (hi := (87581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500219 / 500000) = 1/(500000 / 500219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11675 : Bounds (27369 / 62500000) (87581 / 200000000) (Real.log (500219 / 500000)) := by
  have h := reflection_log_11675_neg
  have he : Real.log (500219 / 500000) = -Real.log (500000 / 500219) := by
    rw [show ((500219 / 500000) : ℝ) = ((500000 / 500219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11676_neg : (87619 / 200000000) ≤ -Real.log (499781 / 500000) ∧
    -Real.log (499781 / 500000) ≤ (27381 / 62500000) := by
  have h := checkLog_sound (w := (219 / 999781)) (n := 12)
    (lo := (87619 / 200000000)) (hi := (27381 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499781) = 1/(499781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11676 : Bounds (-27381 / 62500000) (-87619 / 200000000) (Real.log (499781 / 500000)) := by
  have h := reflection_log_11676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11677_neg : (6374359 / 31250000) ≤ -Real.log (1000000 / 1226273) ∧
    -Real.log (1000000 / 1226273) ≤ (203979489 / 1000000000) := by
  have h := checkLog_sound (w := (226273 / 2226273)) (n := 12)
    (lo := (6374359 / 31250000)) (hi := (203979489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226273 / 1000000) = 1/(1000000 / 1226273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11677 : Bounds (6374359 / 31250000) (203979489 / 1000000000) (Real.log (1226273 / 1000000)) := by
  have h := reflection_log_11677_neg
  have he : Real.log (1226273 / 1000000) = -Real.log (1000000 / 1226273) := by
    rw [show ((1226273 / 1000000) : ℝ) = ((1000000 / 1226273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11678_neg : (12826809 / 50000000) ≤ -Real.log (773727 / 1000000) ∧
    -Real.log (773727 / 1000000) ≤ (256536181 / 1000000000) := by
  have h := checkLog_sound (w := (226273 / 1773727)) (n := 12)
    (lo := (12826809 / 50000000)) (hi := (256536181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773727) = 1/(773727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11678 : Bounds (-256536181 / 1000000000) (-12826809 / 50000000) (Real.log (773727 / 1000000)) := by
  have h := reflection_log_11678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11679_neg : (51194177 / 250000000) ≤ -Real.log (1000000 / 1227251) ∧
    -Real.log (1000000 / 1227251) ≤ (204776709 / 1000000000) := by
  have h := checkLog_sound (w := (227251 / 2227251)) (n := 12)
    (lo := (51194177 / 250000000)) (hi := (204776709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227251 / 1000000) = 1/(1000000 / 1227251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11679 : Bounds (51194177 / 250000000) (204776709 / 1000000000) (Real.log (1227251 / 1000000)) := by
  have h := reflection_log_11679_neg
  have he : Real.log (1227251 / 1000000) = -Real.log (1000000 / 1227251) := by
    rw [show ((1227251 / 1000000) : ℝ) = ((1000000 / 1227251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11680_neg : (8056281 / 31250000) ≤ -Real.log (772749 / 1000000) ∧
    -Real.log (772749 / 1000000) ≤ (257800993 / 1000000000) := by
  have h := checkLog_sound (w := (227251 / 1772749)) (n := 12)
    (lo := (8056281 / 31250000)) (hi := (257800993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772749) = 1/(772749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11680 : Bounds (-257800993 / 1000000000) (-8056281 / 31250000) (Real.log (772749 / 1000000)) := by
  have h := reflection_log_11680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11681_neg : (53024283 / 1000000000) ≤ -Real.log (948356982999 / 1000000000000) ∧
    -Real.log (948356982999 / 1000000000000) ≤ (13256071 / 250000000) := by
  have h := checkLog_sound (w := (51643017001 / 1948356982999)) (n := 12)
    (lo := (53024283 / 1000000000)) (hi := (13256071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948356982999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948356982999) = 1/(948356982999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11681 : Bounds (-13256071 / 250000000) (-53024283 / 1000000000) (Real.log (948356982999 / 1000000000000)) := by
  have h := reflection_log_11681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11682_neg : (13139173 / 250000000) ≤ -Real.log (948800529471 / 1000000000000) ∧
    -Real.log (948800529471 / 1000000000000) ≤ (52556693 / 1000000000) := by
  have h := checkLog_sound (w := (51199470529 / 1948800529471)) (n := 12)
    (lo := (13139173 / 250000000)) (hi := (52556693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948800529471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948800529471) = 1/(948800529471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11682 : Bounds (-52556693 / 1000000000) (-13139173 / 250000000) (Real.log (948800529471 / 1000000000000)) := by
  have h := reflection_log_11682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11683_neg : (115128917 / 250000000) ≤ -Real.log (125000000000 / 198111381663) ∧
    -Real.log (125000000000 / 198111381663) ≤ (460515669 / 1000000000) := by
  have h := checkLog_sound (w := (73111381663 / 323111381663)) (n := 12)
    (lo := (115128917 / 250000000)) (hi := (460515669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198111381663 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198111381663 / 125000000000) = 1/(125000000000 / 198111381663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11683 : Bounds (115128917 / 250000000) (460515669 / 1000000000) (Real.log (198111381663 / 125000000000)) := by
  have h := reflection_log_11683_neg
  have he : Real.log (198111381663 / 125000000000) = -Real.log (125000000000 / 198111381663) := by
    rw [show ((198111381663 / 125000000000) : ℝ) = ((125000000000 / 198111381663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11684_neg : (4625777 / 10000000) ≤ -Real.log (500000000000 / 794081260539) ∧
    -Real.log (500000000000 / 794081260539) ≤ (462577701 / 1000000000) := by
  have h := checkLog_sound (w := (294081260539 / 1294081260539)) (n := 12)
    (lo := (4625777 / 10000000)) (hi := (462577701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794081260539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794081260539 / 500000000000) = 1/(500000000000 / 794081260539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11684 : Bounds (4625777 / 10000000) (462577701 / 1000000000) (Real.log (794081260539 / 500000000000)) := by
  have h := reflection_log_11684_neg
  have he : Real.log (794081260539 / 500000000000) = -Real.log (500000000000 / 794081260539) := by
    rw [show ((794081260539 / 500000000000) : ℝ) = ((500000000000 / 794081260539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11685_neg : (937033257 / 1000000000) ≤ -Real.log (12500000000 / 31904973357) ∧
    -Real.log (12500000000 / 31904973357) ≤ (937033259 / 1000000000) := by
  have h := checkLog_sound (w := (6904973357 / 56904973357)) (n := 12)
    (lo := (243886077 / 1000000000)) (hi := (121943039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31904973357 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31904973357 / 25000000000) = 1/(12500000000 / 31904973357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11685 : Bounds (937033257 / 1000000000) (937033259 / 1000000000) (Real.log (31904973357 / 12500000000)) := by
  have h := reflection_log_11685_neg
  have he : Real.log (31904973357 / 12500000000) = -Real.log (12500000000 / 31904973357) := by
    rw [show ((31904973357 / 12500000000) : ℝ) = ((12500000000 / 31904973357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11686_neg : (939506687 / 1000000000) ≤ -Real.log (100000000000 / 255871886121) ∧
    -Real.log (100000000000 / 255871886121) ≤ (939506689 / 1000000000) := by
  have h := checkLog_sound (w := (55871886121 / 455871886121)) (n := 12)
    (lo := (246359507 / 1000000000)) (hi := (61589877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255871886121 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(255871886121 / 200000000000) = 1/(100000000000 / 255871886121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11686 : Bounds (939506687 / 1000000000) (939506689 / 1000000000) (Real.log (255871886121 / 100000000000)) := by
  have h := reflection_log_11686_neg
  have he : Real.log (255871886121 / 100000000000) = -Real.log (100000000000 / 255871886121) := by
    rw [show ((255871886121 / 100000000000) : ℝ) = ((100000000000 / 255871886121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11687_neg : (363948427 / 1000000000) ≤ -Real.log (1000 / 1439) ∧
    -Real.log (1000 / 1439) ≤ (90987107 / 250000000) := by
  have h := checkLog_sound (w := (439 / 2439)) (n := 12)
    (lo := (363948427 / 1000000000)) (hi := (90987107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1000) = 1/(1000 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11687 : Bounds (363948427 / 1000000000) (90987107 / 250000000) (Real.log (1439 / 1000)) := by
  have h := reflection_log_11687_neg
  have he : Real.log (1439 / 1000) = -Real.log (1000 / 1439) := by
    rw [show ((1439 / 1000) : ℝ) = ((1000 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11688_neg : (578034373 / 1000000000) ≤ -Real.log (561 / 1000) ∧
    -Real.log (561 / 1000) ≤ (289017187 / 500000000) := by
  have h := checkLog_sound (w := (439 / 1561)) (n := 12)
    (lo := (578034373 / 1000000000)) (hi := (289017187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 561) = 1/(561 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11688 : Bounds (-289017187 / 500000000) (-578034373 / 1000000000) (Real.log (561 / 1000)) := by
  have h := reflection_log_11688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11689_neg : (438903 / 1000000000) ≤ -Real.log (1000000 / 1000439) ∧
    -Real.log (1000000 / 1000439) ≤ (54863 / 125000000) := by
  have h := checkLog_sound (w := (439 / 2000439)) (n := 12)
    (lo := (438903 / 1000000000)) (hi := (54863 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000439 / 1000000) = 1/(1000000 / 1000439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11689 : Bounds (438903 / 1000000000) (54863 / 125000000) (Real.log (1000439 / 1000000)) := by
  have h := reflection_log_11689_neg
  have he : Real.log (1000439 / 1000000) = -Real.log (1000000 / 1000439) := by
    rw [show ((1000439 / 1000000) : ℝ) = ((1000000 / 1000439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11690_neg : (54887 / 125000000) ≤ -Real.log (999561 / 1000000) ∧
    -Real.log (999561 / 1000000) ≤ (439097 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1999561)) (n := 12)
    (lo := (54887 / 125000000)) (hi := (439097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999561) = 1/(999561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11690 : Bounds (-439097 / 1000000000) (-54887 / 125000000) (Real.log (999561 / 1000000)) := by
  have h := reflection_log_11690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11691_neg : (204432791 / 1000000000) ≤ -Real.log (1000000 / 1226829) ∧
    -Real.log (1000000 / 1226829) ≤ (25554099 / 125000000) := by
  have h := checkLog_sound (w := (226829 / 2226829)) (n := 12)
    (lo := (204432791 / 1000000000)) (hi := (25554099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226829 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226829 / 1000000) = 1/(1000000 / 1226829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11691 : Bounds (204432791 / 1000000000) (25554099 / 125000000) (Real.log (1226829 / 1000000)) := by
  have h := reflection_log_11691_neg
  have he : Real.log (1226829 / 1000000) = -Real.log (1000000 / 1226829) := by
    rw [show ((1226829 / 1000000) : ℝ) = ((1000000 / 1226829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11692_neg : (128627519 / 500000000) ≤ -Real.log (773171 / 1000000) ∧
    -Real.log (773171 / 1000000) ≤ (257255039 / 1000000000) := by
  have h := checkLog_sound (w := (226829 / 1773171)) (n := 12)
    (lo := (128627519 / 500000000)) (hi := (257255039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773171) = 1/(773171 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11692 : Bounds (-257255039 / 1000000000) (-128627519 / 500000000) (Real.log (773171 / 1000000)) := by
  have h := reflection_log_11692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11693_neg : (2565391 / 12500000) ≤ -Real.log (1000000 / 1227809) ∧
    -Real.log (1000000 / 1227809) ≤ (205231281 / 1000000000) := by
  have h := checkLog_sound (w := (227809 / 2227809)) (n := 12)
    (lo := (2565391 / 12500000)) (hi := (205231281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227809 / 1000000) = 1/(1000000 / 1227809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11693 : Bounds (2565391 / 12500000) (205231281 / 1000000000) (Real.log (1227809 / 1000000)) := by
  have h := reflection_log_11693_neg
  have he : Real.log (1227809 / 1000000) = -Real.log (1000000 / 1227809) := by
    rw [show ((1227809 / 1000000) : ℝ) = ((1000000 / 1227809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11694_neg : (5170467 / 20000000) ≤ -Real.log (772191 / 1000000) ∧
    -Real.log (772191 / 1000000) ≤ (258523351 / 1000000000) := by
  have h := checkLog_sound (w := (227809 / 1772191)) (n := 12)
    (lo := (5170467 / 20000000)) (hi := (258523351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772191) = 1/(772191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11694 : Bounds (-258523351 / 1000000000) (-5170467 / 20000000) (Real.log (772191 / 1000000)) := by
  have h := reflection_log_11694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11695_neg : (5329207 / 100000000) ≤ -Real.log (948103059519 / 1000000000000) ∧
    -Real.log (948103059519 / 1000000000000) ≤ (53292071 / 1000000000) := by
  have h := checkLog_sound (w := (51896940481 / 1948103059519)) (n := 12)
    (lo := (5329207 / 100000000)) (hi := (53292071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948103059519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948103059519) = 1/(948103059519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11695 : Bounds (-53292071 / 1000000000) (-5329207 / 100000000) (Real.log (948103059519 / 1000000000000)) := by
  have h := reflection_log_11695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11696_neg : (52822247 / 1000000000) ≤ -Real.log (948548604759 / 1000000000000) ∧
    -Real.log (948548604759 / 1000000000000) ≤ (6602781 / 125000000) := by
  have h := checkLog_sound (w := (51451395241 / 1948548604759)) (n := 12)
    (lo := (52822247 / 1000000000)) (hi := (6602781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948548604759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948548604759) = 1/(948548604759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11696 : Bounds (-6602781 / 125000000) (-52822247 / 1000000000) (Real.log (948548604759 / 1000000000000)) := by
  have h := reflection_log_11696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11697_neg : (46168783 / 100000000) ≤ -Real.log (125000000000 / 198343736379) ∧
    -Real.log (125000000000 / 198343736379) ≤ (461687831 / 1000000000) := by
  have h := checkLog_sound (w := (73343736379 / 323343736379)) (n := 12)
    (lo := (46168783 / 100000000)) (hi := (461687831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198343736379 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198343736379 / 125000000000) = 1/(125000000000 / 198343736379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11697 : Bounds (46168783 / 100000000) (461687831 / 1000000000) (Real.log (198343736379 / 125000000000)) := by
  have h := reflection_log_11697_neg
  have he : Real.log (198343736379 / 125000000000) = -Real.log (125000000000 / 198343736379) := by
    rw [show ((198343736379 / 125000000000) : ℝ) = ((125000000000 / 198343736379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11698_neg : (46375463 / 100000000) ≤ -Real.log (500000000000 / 795016388433) ∧
    -Real.log (500000000000 / 795016388433) ≤ (463754631 / 1000000000) := by
  have h := checkLog_sound (w := (295016388433 / 1295016388433)) (n := 12)
    (lo := (46375463 / 100000000)) (hi := (463754631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795016388433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795016388433 / 500000000000) = 1/(500000000000 / 795016388433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11698 : Bounds (46375463 / 100000000) (463754631 / 1000000000) (Real.log (795016388433 / 500000000000)) := by
  have h := reflection_log_11698_neg
  have he : Real.log (795016388433 / 500000000000) = -Real.log (500000000000 / 795016388433) := by
    rw [show ((795016388433 / 500000000000) : ℝ) = ((500000000000 / 795016388433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11699_neg : (939506687 / 1000000000) ≤ -Real.log (125000000000 / 319839857651) ∧
    -Real.log (125000000000 / 319839857651) ≤ (939506689 / 1000000000) := by
  have h := checkLog_sound (w := (69839857651 / 569839857651)) (n := 12)
    (lo := (246359507 / 1000000000)) (hi := (61589877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319839857651 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(319839857651 / 250000000000) = 1/(125000000000 / 319839857651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11699 : Bounds (939506687 / 1000000000) (939506689 / 1000000000) (Real.log (319839857651 / 125000000000)) := by
  have h := reflection_log_11699_neg
  have he : Real.log (319839857651 / 125000000000) = -Real.log (125000000000 / 319839857651) := by
    rw [show ((319839857651 / 125000000000) : ℝ) = ((125000000000 / 319839857651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11700_neg : (2354957 / 2500000) ≤ -Real.log (62500000000 / 160316399287) ∧
    -Real.log (62500000000 / 160316399287) ≤ (470991401 / 500000000) := by
  have h := checkLog_sound (w := (35316399287 / 285316399287)) (n := 12)
    (lo := (12441781 / 50000000)) (hi := (248835621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160316399287 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160316399287 / 125000000000) = 1/(62500000000 / 160316399287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11700 : Bounds (2354957 / 2500000) (470991401 / 500000000) (Real.log (160316399287 / 62500000000)) := by
  have h := reflection_log_11700_neg
  have he : Real.log (160316399287 / 62500000000) = -Real.log (62500000000 / 160316399287) := by
    rw [show ((160316399287 / 62500000000) : ℝ) = ((62500000000 / 160316399287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11701_neg : (364643113 / 1000000000) ≤ -Real.log (25 / 36) ∧
    -Real.log (25 / 36) ≤ (182321557 / 500000000) := by
  have h := checkLog_sound (w := (11 / 61)) (n := 12)
    (lo := (364643113 / 1000000000)) (hi := (182321557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36 / 25) = 1/(25 / 36) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11701 : Bounds (364643113 / 1000000000) (182321557 / 500000000) (Real.log (36 / 25)) := by
  have h := reflection_log_11701_neg
  have he : Real.log (36 / 25) = -Real.log (25 / 36) := by
    rw [show ((36 / 25) : ℝ) = ((25 / 36) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11702_neg : (115963699 / 200000000) ≤ -Real.log (14 / 25) ∧
    -Real.log (14 / 25) ≤ (1132458 / 1953125) := by
  have h := checkLog_sound (w := (11 / 39)) (n := 12)
    (lo := (115963699 / 200000000)) (hi := (1132458 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 14) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 14) = 1/(14 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11702 : Bounds (-1132458 / 1953125) (-115963699 / 200000000) (Real.log (14 / 25)) := by
  have h := reflection_log_11702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11703_neg : (439903 / 1000000000) ≤ -Real.log (25000 / 25011) ∧
    -Real.log (25000 / 25011) ≤ (13747 / 31250000) := by
  have h := checkLog_sound (w := (11 / 50011)) (n := 12)
    (lo := (439903 / 1000000000)) (hi := (13747 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25011 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25011 / 25000) = 1/(25000 / 25011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11703 : Bounds (439903 / 1000000000) (13747 / 31250000) (Real.log (25011 / 25000)) := by
  have h := reflection_log_11703_neg
  have he : Real.log (25011 / 25000) = -Real.log (25000 / 25011) := by
    rw [show ((25011 / 25000) : ℝ) = ((25000 / 25011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11704_neg : (13753 / 31250000) ≤ -Real.log (24989 / 25000) ∧
    -Real.log (24989 / 25000) ≤ (440097 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 49989)) (n := 12)
    (lo := (13753 / 31250000)) (hi := (440097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24989) = 1/(24989 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11704 : Bounds (-440097 / 1000000000) (-13753 / 31250000) (Real.log (24989 / 25000)) := by
  have h := reflection_log_11704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11705_neg : (12805419 / 62500000) ≤ -Real.log (500000 / 613693) ∧
    -Real.log (500000 / 613693) ≤ (40977341 / 200000000) := by
  have h := checkLog_sound (w := (113693 / 1113693)) (n := 12)
    (lo := (12805419 / 62500000)) (hi := (40977341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613693 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613693 / 500000) = 1/(500000 / 613693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11705 : Bounds (12805419 / 62500000) (40977341 / 200000000) (Real.log (613693 / 500000)) := by
  have h := reflection_log_11705_neg
  have he : Real.log (613693 / 500000) = -Real.log (500000 / 613693) := by
    rw [show ((613693 / 500000) : ℝ) = ((500000 / 613693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11706_neg : (64493927 / 250000000) ≤ -Real.log (386307 / 500000) ∧
    -Real.log (386307 / 500000) ≤ (257975709 / 1000000000) := by
  have h := checkLog_sound (w := (113693 / 886307)) (n := 12)
    (lo := (64493927 / 250000000)) (hi := (257975709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386307) = 1/(386307 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11706 : Bounds (-257975709 / 1000000000) (-64493927 / 250000000) (Real.log (386307 / 500000)) := by
  have h := reflection_log_11706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11707_neg : (205686459 / 1000000000) ≤ -Real.log (62500 / 76773) ∧
    -Real.log (62500 / 76773) ≤ (10284323 / 50000000) := by
  have h := checkLog_sound (w := (14273 / 139273)) (n := 12)
    (lo := (205686459 / 1000000000)) (hi := (10284323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76773 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76773 / 62500) = 1/(62500 / 76773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11707 : Bounds (205686459 / 1000000000) (10284323 / 50000000) (Real.log (76773 / 62500)) := by
  have h := reflection_log_11707_neg
  have he : Real.log (76773 / 62500) = -Real.log (62500 / 76773) := by
    rw [show ((76773 / 62500) : ℝ) = ((62500 / 76773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11708_neg : (129623763 / 500000000) ≤ -Real.log (48227 / 62500) ∧
    -Real.log (48227 / 62500) ≤ (259247527 / 1000000000) := by
  have h := checkLog_sound (w := (14273 / 110727)) (n := 12)
    (lo := (129623763 / 500000000)) (hi := (259247527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48227) = 1/(48227 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11708 : Bounds (-259247527 / 1000000000) (-129623763 / 500000000) (Real.log (48227 / 62500)) := by
  have h := reflection_log_11708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11709_neg : (53561067 / 1000000000) ≤ -Real.log (3702531471 / 3906250000) ∧
    -Real.log (3702531471 / 3906250000) ≤ (13390267 / 250000000) := by
  have h := checkLog_sound (w := (203718529 / 7608781471)) (n := 12)
    (lo := (53561067 / 1000000000)) (hi := (13390267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3702531471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3702531471) = 1/(3702531471 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11709 : Bounds (-13390267 / 250000000) (-53561067 / 1000000000) (Real.log (3702531471 / 3906250000)) := by
  have h := reflection_log_11709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11710_neg : (53089003 / 1000000000) ≤ -Real.log (237073901751 / 250000000000) ∧
    -Real.log (237073901751 / 250000000000) ≤ (13272251 / 250000000) := by
  have h := checkLog_sound (w := (12926098249 / 487073901751)) (n := 12)
    (lo := (53089003 / 1000000000)) (hi := (13272251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237073901751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237073901751) = 1/(237073901751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11710 : Bounds (-13272251 / 250000000) (-53089003 / 1000000000) (Real.log (237073901751 / 250000000000)) := by
  have h := reflection_log_11710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11711_neg : (115715603 / 250000000) ≤ -Real.log (500000000000 / 794307377293) ∧
    -Real.log (500000000000 / 794307377293) ≤ (462862413 / 1000000000) := by
  have h := checkLog_sound (w := (294307377293 / 1294307377293)) (n := 12)
    (lo := (115715603 / 250000000)) (hi := (462862413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794307377293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794307377293 / 500000000000) = 1/(500000000000 / 794307377293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11711 : Bounds (115715603 / 250000000) (462862413 / 1000000000) (Real.log (794307377293 / 500000000000)) := by
  have h := reflection_log_11711_neg
  have he : Real.log (794307377293 / 500000000000) = -Real.log (500000000000 / 794307377293) := by
    rw [show ((794307377293 / 500000000000) : ℝ) = ((500000000000 / 794307377293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0183 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11712_neg : (92986797 / 200000000) ≤ -Real.log (500000000000 / 795954548283) ∧
    -Real.log (500000000000 / 795954548283) ≤ (232466993 / 500000000) := by
  have h := checkLog_sound (w := (295954548283 / 1295954548283)) (n := 12)
    (lo := (92986797 / 200000000)) (hi := (232466993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795954548283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795954548283 / 500000000000) = 1/(500000000000 / 795954548283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11712 : Bounds (92986797 / 200000000) (232466993 / 500000000) (Real.log (795954548283 / 500000000000)) := by
  have h := reflection_log_11712_neg
  have he : Real.log (795954548283 / 500000000000) = -Real.log (500000000000 / 795954548283) := by
    rw [show ((795954548283 / 500000000000) : ℝ) = ((500000000000 / 795954548283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11713_neg : (2354957 / 2500000) ≤ -Real.log (100000000000 / 256506238859) ∧
    -Real.log (100000000000 / 256506238859) ≤ (470991401 / 500000000) := by
  have h := checkLog_sound (w := (56506238859 / 456506238859)) (n := 12)
    (lo := (12441781 / 50000000)) (hi := (248835621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256506238859 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256506238859 / 200000000000) = 1/(100000000000 / 256506238859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11713 : Bounds (2354957 / 2500000) (470991401 / 500000000) (Real.log (256506238859 / 100000000000)) := by
  have h := reflection_log_11713_neg
  have he : Real.log (256506238859 / 100000000000) = -Real.log (100000000000 / 256506238859) := by
    rw [show ((256506238859 / 100000000000) : ℝ) = ((100000000000 / 256506238859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11714_neg : (118057701 / 125000000) ≤ -Real.log (100000000000 / 257142857143) ∧
    -Real.log (100000000000 / 257142857143) ≤ (94446161 / 100000000) := by
  have h := checkLog_sound (w := (57142857143 / 457142857143)) (n := 12)
    (lo := (62828607 / 250000000)) (hi := (251314429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257142857143 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(257142857143 / 200000000000) = 1/(100000000000 / 257142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11714 : Bounds (118057701 / 125000000) (94446161 / 100000000) (Real.log (257142857143 / 100000000000)) := by
  have h := reflection_log_11714_neg
  have he : Real.log (257142857143 / 100000000000) = -Real.log (100000000000 / 257142857143) := by
    rw [show ((257142857143 / 100000000000) : ℝ) = ((100000000000 / 257142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11715_neg : (365337317 / 1000000000) ≤ -Real.log (1000 / 1441) ∧
    -Real.log (1000 / 1441) ≤ (182668659 / 500000000) := by
  have h := checkLog_sound (w := (441 / 2441)) (n := 12)
    (lo := (365337317 / 1000000000)) (hi := (182668659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441 / 1000) = 1/(1000 / 1441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11715 : Bounds (365337317 / 1000000000) (182668659 / 500000000) (Real.log (1441 / 1000)) := by
  have h := reflection_log_11715_neg
  have he : Real.log (1441 / 1000) = -Real.log (1000 / 1441) := by
    rw [show ((1441 / 1000) : ℝ) = ((1000 / 1441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11716_neg : (116321161 / 200000000) ≤ -Real.log (559 / 1000) ∧
    -Real.log (559 / 1000) ≤ (290802903 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1559)) (n := 12)
    (lo := (116321161 / 200000000)) (hi := (290802903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 559) = 1/(559 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11716 : Bounds (-290802903 / 500000000) (-116321161 / 200000000) (Real.log (559 / 1000)) := by
  have h := reflection_log_11716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11717_neg : (220451 / 500000000) ≤ -Real.log (1000000 / 1000441) ∧
    -Real.log (1000000 / 1000441) ≤ (440903 / 1000000000) := by
  have h := checkLog_sound (w := (441 / 2000441)) (n := 12)
    (lo := (220451 / 500000000)) (hi := (440903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000441 / 1000000) = 1/(1000000 / 1000441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11717 : Bounds (220451 / 500000000) (440903 / 1000000000) (Real.log (1000441 / 1000000)) := by
  have h := reflection_log_11717_neg
  have he : Real.log (1000441 / 1000000) = -Real.log (1000000 / 1000441) := by
    rw [show ((1000441 / 1000000) : ℝ) = ((1000000 / 1000441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11718_neg : (441097 / 1000000000) ≤ -Real.log (999559 / 1000000) ∧
    -Real.log (999559 / 1000000) ≤ (220549 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1999559)) (n := 12)
    (lo := (441097 / 1000000000)) (hi := (220549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999559) = 1/(999559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11718 : Bounds (-220549 / 500000000) (-441097 / 1000000000) (Real.log (999559 / 1000000)) := by
  have h := reflection_log_11718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11719_neg : (102670613 / 500000000) ≤ -Real.log (125000 / 153493) ∧
    -Real.log (125000 / 153493) ≤ (205341227 / 1000000000) := by
  have h := checkLog_sound (w := (28493 / 278493)) (n := 12)
    (lo := (102670613 / 500000000)) (hi := (205341227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153493 / 125000) = 1/(125000 / 153493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11719 : Bounds (102670613 / 500000000) (205341227 / 1000000000) (Real.log (153493 / 125000)) := by
  have h := reflection_log_11719_neg
  have he : Real.log (153493 / 125000) = -Real.log (125000 / 153493) := by
    rw [show ((153493 / 125000) : ℝ) = ((125000 / 153493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11720_neg : (16168637 / 62500000) ≤ -Real.log (96507 / 125000) ∧
    -Real.log (96507 / 125000) ≤ (258698193 / 1000000000) := by
  have h := checkLog_sound (w := (28493 / 221507)) (n := 12)
    (lo := (16168637 / 62500000)) (hi := (258698193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96507) = 1/(96507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11720 : Bounds (-258698193 / 1000000000) (-16168637 / 62500000) (Real.log (96507 / 125000)) := by
  have h := reflection_log_11720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11721_neg : (206140617 / 1000000000) ≤ -Real.log (500000 / 614463) ∧
    -Real.log (500000 / 614463) ≤ (103070309 / 500000000) := by
  have h := checkLog_sound (w := (114463 / 1114463)) (n := 12)
    (lo := (206140617 / 1000000000)) (hi := (103070309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614463 / 500000) = 1/(500000 / 614463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11721 : Bounds (206140617 / 1000000000) (103070309 / 500000000) (Real.log (614463 / 500000)) := by
  have h := reflection_log_11721_neg
  have he : Real.log (614463 / 500000) = -Real.log (500000 / 614463) := by
    rw [show ((614463 / 500000) : ℝ) = ((500000 / 614463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11722_neg : (25997093 / 100000000) ≤ -Real.log (385537 / 500000) ∧
    -Real.log (385537 / 500000) ≤ (259970931 / 1000000000) := by
  have h := checkLog_sound (w := (114463 / 885537)) (n := 12)
    (lo := (25997093 / 100000000)) (hi := (259970931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385537) = 1/(385537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11722 : Bounds (-259970931 / 1000000000) (-25997093 / 100000000) (Real.log (385537 / 500000)) := by
  have h := reflection_log_11722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11723_neg : (53830313 / 1000000000) ≤ -Real.log (236898221631 / 250000000000) ∧
    -Real.log (236898221631 / 250000000000) ≤ (26915157 / 500000000) := by
  have h := checkLog_sound (w := (13101778369 / 486898221631)) (n := 12)
    (lo := (53830313 / 1000000000)) (hi := (26915157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236898221631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236898221631) = 1/(236898221631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11723 : Bounds (-26915157 / 500000000) (-53830313 / 1000000000) (Real.log (236898221631 / 250000000000)) := by
  have h := reflection_log_11723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11724_neg : (26678483 / 500000000) ≤ -Real.log (14813148951 / 15625000000) ∧
    -Real.log (14813148951 / 15625000000) ≤ (53356967 / 1000000000) := by
  have h := checkLog_sound (w := (811851049 / 30438148951)) (n := 12)
    (lo := (26678483 / 500000000)) (hi := (53356967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14813148951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14813148951) = 1/(14813148951 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11724 : Bounds (-53356967 / 1000000000) (-26678483 / 500000000) (Real.log (14813148951 / 15625000000)) := by
  have h := reflection_log_11724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11725_neg : (232019709 / 500000000) ≤ -Real.log (250000000000 / 397621416063) ∧
    -Real.log (250000000000 / 397621416063) ≤ (464039419 / 1000000000) := by
  have h := checkLog_sound (w := (147621416063 / 647621416063)) (n := 12)
    (lo := (232019709 / 500000000)) (hi := (464039419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397621416063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397621416063 / 250000000000) = 1/(250000000000 / 397621416063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11725 : Bounds (232019709 / 500000000) (464039419 / 1000000000) (Real.log (397621416063 / 250000000000)) := by
  have h := reflection_log_11725_neg
  have he : Real.log (397621416063 / 250000000000) = -Real.log (250000000000 / 397621416063) := by
    rw [show ((397621416063 / 250000000000) : ℝ) = ((250000000000 / 397621416063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11726_neg : (466111547 / 1000000000) ≤ -Real.log (15625000000 / 24902887077) ∧
    -Real.log (15625000000 / 24902887077) ≤ (116527887 / 250000000) := by
  have h := checkLog_sound (w := (9277887077 / 40527887077)) (n := 12)
    (lo := (466111547 / 1000000000)) (hi := (116527887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24902887077 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24902887077 / 15625000000) = 1/(15625000000 / 24902887077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11726 : Bounds (466111547 / 1000000000) (116527887 / 250000000) (Real.log (24902887077 / 15625000000)) := by
  have h := reflection_log_11726_neg
  have he : Real.log (24902887077 / 15625000000) = -Real.log (15625000000 / 24902887077) := by
    rw [show ((24902887077 / 15625000000) : ℝ) = ((15625000000 / 24902887077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11727_neg : (118057701 / 125000000) ≤ -Real.log (250000000000 / 642857142857) ∧
    -Real.log (250000000000 / 642857142857) ≤ (94446161 / 100000000) := by
  have h := checkLog_sound (w := (142857142857 / 1142857142857)) (n := 12)
    (lo := (62828607 / 250000000)) (hi := (251314429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642857142857 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(642857142857 / 500000000000) = 1/(250000000000 / 642857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11727 : Bounds (118057701 / 125000000) (94446161 / 100000000) (Real.log (642857142857 / 250000000000)) := by
  have h := reflection_log_11727_neg
  have he : Real.log (642857142857 / 250000000000) = -Real.log (250000000000 / 642857142857) := by
    rw [show ((642857142857 / 250000000000) : ℝ) = ((250000000000 / 642857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11728_neg : (473471561 / 500000000) ≤ -Real.log (500000000000 / 1288908765653) ∧
    -Real.log (500000000000 / 1288908765653) ≤ (236735781 / 250000000) := by
  have h := checkLog_sound (w := (288908765653 / 2288908765653)) (n := 12)
    (lo := (126897971 / 500000000)) (hi := (253795943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288908765653 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1288908765653 / 1000000000000) = 1/(500000000000 / 1288908765653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11728 : Bounds (473471561 / 500000000) (236735781 / 250000000) (Real.log (1288908765653 / 500000000000)) := by
  have h := reflection_log_11728_neg
  have he : Real.log (1288908765653 / 500000000000) = -Real.log (500000000000 / 1288908765653) := by
    rw [show ((1288908765653 / 500000000000) : ℝ) = ((500000000000 / 1288908765653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11729_neg : (183015519 / 500000000) ≤ -Real.log (500 / 721) ∧
    -Real.log (500 / 721) ≤ (366031039 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1221)) (n := 12)
    (lo := (183015519 / 500000000)) (hi := (366031039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 500) = 1/(500 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11729 : Bounds (183015519 / 500000000) (366031039 / 1000000000) (Real.log (721 / 500)) := by
  have h := reflection_log_11729_neg
  have he : Real.log (721 / 500) = -Real.log (500 / 721) := by
    rw [show ((721 / 500) : ℝ) = ((500 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11730_neg : (145849079 / 250000000) ≤ -Real.log (279 / 500) ∧
    -Real.log (279 / 500) ≤ (583396317 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 779)) (n := 12)
    (lo := (145849079 / 250000000)) (hi := (583396317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 279) = 1/(279 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11730 : Bounds (-583396317 / 1000000000) (-145849079 / 250000000) (Real.log (279 / 500)) := by
  have h := reflection_log_11730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11731_neg : (220951 / 500000000) ≤ -Real.log (500000 / 500221) ∧
    -Real.log (500000 / 500221) ≤ (441903 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1000221)) (n := 12)
    (lo := (220951 / 500000000)) (hi := (441903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500221 / 500000) = 1/(500000 / 500221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11731 : Bounds (220951 / 500000000) (441903 / 1000000000) (Real.log (500221 / 500000)) := by
  have h := reflection_log_11731_neg
  have he : Real.log (500221 / 500000) = -Real.log (500000 / 500221) := by
    rw [show ((500221 / 500000) : ℝ) = ((500000 / 500221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11732_neg : (442097 / 1000000000) ≤ -Real.log (499779 / 500000) ∧
    -Real.log (499779 / 500000) ≤ (221049 / 500000000) := by
  have h := checkLog_sound (w := (221 / 999779)) (n := 12)
    (lo := (442097 / 1000000000)) (hi := (221049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499779) = 1/(499779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11732 : Bounds (-221049 / 500000000) (-442097 / 1000000000) (Real.log (499779 / 500000)) := by
  have h := reflection_log_11732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11733_neg : (10289777 / 50000000) ≤ -Real.log (500000 / 614251) ∧
    -Real.log (500000 / 614251) ≤ (205795541 / 1000000000) := by
  have h := checkLog_sound (w := (114251 / 1114251)) (n := 12)
    (lo := (10289777 / 50000000)) (hi := (205795541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614251 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614251 / 500000) = 1/(500000 / 614251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11733 : Bounds (10289777 / 50000000) (205795541 / 1000000000) (Real.log (614251 / 500000)) := by
  have h := reflection_log_11733_neg
  have he : Real.log (614251 / 500000) = -Real.log (500000 / 614251) := by
    rw [show ((614251 / 500000) : ℝ) = ((500000 / 614251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11734_neg : (259421199 / 1000000000) ≤ -Real.log (385749 / 500000) ∧
    -Real.log (385749 / 500000) ≤ (648553 / 2500000) := by
  have h := checkLog_sound (w := (114251 / 885749)) (n := 12)
    (lo := (259421199 / 1000000000)) (hi := (648553 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385749) = 1/(385749 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11734 : Bounds (-648553 / 2500000) (-259421199 / 1000000000) (Real.log (385749 / 500000)) := by
  have h := reflection_log_11734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11735_neg : (103297691 / 500000000) ≤ -Real.log (200000 / 245897) ∧
    -Real.log (200000 / 245897) ≤ (206595383 / 1000000000) := by
  have h := checkLog_sound (w := (45897 / 445897)) (n := 12)
    (lo := (103297691 / 500000000)) (hi := (206595383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245897 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245897 / 200000) = 1/(200000 / 245897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11735 : Bounds (103297691 / 500000000) (206595383 / 1000000000) (Real.log (245897 / 200000)) := by
  have h := reflection_log_11735_neg
  have he : Real.log (245897 / 200000) = -Real.log (200000 / 245897) := by
    rw [show ((245897 / 200000) : ℝ) = ((200000 / 245897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11736_neg : (65174039 / 250000000) ≤ -Real.log (154103 / 200000) ∧
    -Real.log (154103 / 200000) ≤ (260696157 / 1000000000) := by
  have h := checkLog_sound (w := (45897 / 354103)) (n := 12)
    (lo := (65174039 / 250000000)) (hi := (260696157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154103) = 1/(154103 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11736 : Bounds (-260696157 / 1000000000) (-65174039 / 250000000) (Real.log (154103 / 200000)) := by
  have h := reflection_log_11736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11737_neg : (27050387 / 500000000) ≤ -Real.log (37893465391 / 40000000000) ∧
    -Real.log (37893465391 / 40000000000) ≤ (2164031 / 40000000) := by
  have h := checkLog_sound (w := (2106534609 / 77893465391)) (n := 12)
    (lo := (27050387 / 500000000)) (hi := (2164031 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37893465391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37893465391) = 1/(37893465391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11737 : Bounds (-2164031 / 40000000) (-27050387 / 500000000) (Real.log (37893465391 / 40000000000)) := by
  have h := reflection_log_11737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11738_neg : (26812829 / 500000000) ≤ -Real.log (236946708999 / 250000000000) ∧
    -Real.log (236946708999 / 250000000000) ≤ (53625659 / 1000000000) := by
  have h := checkLog_sound (w := (13053291001 / 486946708999)) (n := 12)
    (lo := (26812829 / 500000000)) (hi := (53625659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236946708999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236946708999) = 1/(236946708999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11738 : Bounds (-53625659 / 1000000000) (-26812829 / 500000000) (Real.log (236946708999 / 250000000000)) := by
  have h := reflection_log_11738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11739_neg : (23260837 / 50000000) ≤ -Real.log (7812500000 / 12440306877) ∧
    -Real.log (7812500000 / 12440306877) ≤ (465216741 / 1000000000) := by
  have h := checkLog_sound (w := (4627806877 / 20252806877)) (n := 12)
    (lo := (23260837 / 50000000)) (hi := (465216741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12440306877 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12440306877 / 7812500000) = 1/(7812500000 / 12440306877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11739 : Bounds (23260837 / 50000000) (465216741 / 1000000000) (Real.log (12440306877 / 7812500000)) := by
  have h := reflection_log_11739_neg
  have he : Real.log (12440306877 / 7812500000) = -Real.log (7812500000 / 12440306877) := by
    rw [show ((12440306877 / 7812500000) : ℝ) = ((7812500000 / 12440306877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11740_neg : (467291539 / 1000000000) ≤ -Real.log (500000000000 / 797833267361) ∧
    -Real.log (500000000000 / 797833267361) ≤ (23364577 / 50000000) := by
  have h := checkLog_sound (w := (297833267361 / 1297833267361)) (n := 12)
    (lo := (467291539 / 1000000000)) (hi := (23364577 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797833267361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797833267361 / 500000000000) = 1/(500000000000 / 797833267361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11740 : Bounds (467291539 / 1000000000) (23364577 / 50000000) (Real.log (797833267361 / 500000000000)) := by
  have h := reflection_log_11740_neg
  have he : Real.log (797833267361 / 500000000000) = -Real.log (500000000000 / 797833267361) := by
    rw [show ((797833267361 / 500000000000) : ℝ) = ((500000000000 / 797833267361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11741_neg : (473471561 / 500000000) ≤ -Real.log (125000000000 / 322227191413) ∧
    -Real.log (125000000000 / 322227191413) ≤ (236735781 / 250000000) := by
  have h := checkLog_sound (w := (72227191413 / 572227191413)) (n := 12)
    (lo := (126897971 / 500000000)) (hi := (253795943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322227191413 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(322227191413 / 250000000000) = 1/(125000000000 / 322227191413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11741 : Bounds (473471561 / 500000000) (236735781 / 250000000) (Real.log (322227191413 / 125000000000)) := by
  have h := reflection_log_11741_neg
  have he : Real.log (322227191413 / 125000000000) = -Real.log (125000000000 / 322227191413) := by
    rw [show ((322227191413 / 125000000000) : ℝ) = ((125000000000 / 322227191413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11742_neg : (474713677 / 500000000) ≤ -Real.log (500000000000 / 1292114695341) ∧
    -Real.log (500000000000 / 1292114695341) ≤ (237356839 / 250000000) := by
  have h := checkLog_sound (w := (292114695341 / 2292114695341)) (n := 12)
    (lo := (128140087 / 500000000)) (hi := (10251207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292114695341 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1292114695341 / 1000000000000) = 1/(500000000000 / 1292114695341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11742 : Bounds (474713677 / 500000000) (237356839 / 250000000) (Real.log (1292114695341 / 500000000000)) := by
  have h := reflection_log_11742_neg
  have he : Real.log (1292114695341 / 500000000000) = -Real.log (500000000000 / 1292114695341) := by
    rw [show ((1292114695341 / 500000000000) : ℝ) = ((500000000000 / 1292114695341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11743_neg : (366724279 / 1000000000) ≤ -Real.log (1000 / 1443) ∧
    -Real.log (1000 / 1443) ≤ (9168107 / 25000000) := by
  have h := checkLog_sound (w := (443 / 2443)) (n := 12)
    (lo := (366724279 / 1000000000)) (hi := (9168107 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443 / 1000) = 1/(1000 / 1443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11743 : Bounds (366724279 / 1000000000) (9168107 / 25000000) (Real.log (1443 / 1000)) := by
  have h := reflection_log_11743_neg
  have he : Real.log (1443 / 1000) = -Real.log (1000 / 1443) := by
    rw [show ((1443 / 1000) : ℝ) = ((1000 / 1443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11744_neg : (585190039 / 1000000000) ≤ -Real.log (557 / 1000) ∧
    -Real.log (557 / 1000) ≤ (14629751 / 25000000) := by
  have h := checkLog_sound (w := (443 / 1557)) (n := 12)
    (lo := (585190039 / 1000000000)) (hi := (14629751 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 557) = 1/(557 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11744 : Bounds (-14629751 / 25000000) (-585190039 / 1000000000) (Real.log (557 / 1000)) := by
  have h := reflection_log_11744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11745_neg : (442901 / 1000000000) ≤ -Real.log (1000000 / 1000443) ∧
    -Real.log (1000000 / 1000443) ≤ (221451 / 500000000) := by
  have h := checkLog_sound (w := (443 / 2000443)) (n := 12)
    (lo := (442901 / 1000000000)) (hi := (221451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000443 / 1000000) = 1/(1000000 / 1000443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11745 : Bounds (442901 / 1000000000) (221451 / 500000000) (Real.log (1000443 / 1000000)) := by
  have h := reflection_log_11745_neg
  have he : Real.log (1000443 / 1000000) = -Real.log (1000000 / 1000443) := by
    rw [show ((1000443 / 1000000) : ℝ) = ((1000000 / 1000443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11746_neg : (221549 / 500000000) ≤ -Real.log (999557 / 1000000) ∧
    -Real.log (999557 / 1000000) ≤ (443099 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 1999557)) (n := 12)
    (lo := (221549 / 500000000)) (hi := (443099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999557) = 1/(999557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11746 : Bounds (-443099 / 1000000000) (-221549 / 500000000) (Real.log (999557 / 1000000)) := by
  have h := reflection_log_11746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11747_neg : (41249767 / 200000000) ≤ -Real.log (1000000 / 1229059) ∧
    -Real.log (1000000 / 1229059) ≤ (51562209 / 250000000) := by
  have h := checkLog_sound (w := (229059 / 2229059)) (n := 12)
    (lo := (41249767 / 200000000)) (hi := (51562209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229059 / 1000000) = 1/(1000000 / 1229059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11747 : Bounds (41249767 / 200000000) (51562209 / 250000000) (Real.log (1229059 / 1000000)) := by
  have h := reflection_log_11747_neg
  have he : Real.log (1229059 / 1000000) = -Real.log (1000000 / 1229059) := by
    rw [show ((1229059 / 1000000) : ℝ) = ((1000000 / 1229059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11748_neg : (32517929 / 125000000) ≤ -Real.log (770941 / 1000000) ∧
    -Real.log (770941 / 1000000) ≤ (260143433 / 1000000000) := by
  have h := checkLog_sound (w := (229059 / 1770941)) (n := 12)
    (lo := (32517929 / 125000000)) (hi := (260143433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770941) = 1/(770941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11748 : Bounds (-260143433 / 1000000000) (-32517929 / 125000000) (Real.log (770941 / 1000000)) := by
  have h := reflection_log_11748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11749_neg : (207049941 / 1000000000) ≤ -Real.log (250000 / 307511) ∧
    -Real.log (250000 / 307511) ≤ (103524971 / 500000000) := by
  have h := checkLog_sound (w := (57511 / 557511)) (n := 12)
    (lo := (207049941 / 1000000000)) (hi := (103524971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307511 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307511 / 250000) = 1/(250000 / 307511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11749 : Bounds (207049941 / 1000000000) (103524971 / 500000000) (Real.log (307511 / 250000)) := by
  have h := reflection_log_11749_neg
  have he : Real.log (307511 / 250000) = -Real.log (250000 / 307511) := by
    rw [show ((307511 / 250000) : ℝ) = ((250000 / 307511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11750_neg : (65355477 / 250000000) ≤ -Real.log (192489 / 250000) ∧
    -Real.log (192489 / 250000) ≤ (261421909 / 1000000000) := by
  have h := checkLog_sound (w := (57511 / 442489)) (n := 12)
    (lo := (65355477 / 250000000)) (hi := (261421909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192489) = 1/(192489 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11750 : Bounds (-261421909 / 1000000000) (-65355477 / 250000000) (Real.log (192489 / 250000)) := by
  have h := reflection_log_11750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11751_neg : (54371967 / 1000000000) ≤ -Real.log (59192484879 / 62500000000) ∧
    -Real.log (59192484879 / 62500000000) ≤ (424781 / 7812500) := by
  have h := checkLog_sound (w := (3307515121 / 121692484879)) (n := 12)
    (lo := (54371967 / 1000000000)) (hi := (424781 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59192484879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59192484879) = 1/(59192484879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11751 : Bounds (-424781 / 7812500) (-54371967 / 1000000000) (Real.log (59192484879 / 62500000000)) := by
  have h := reflection_log_11751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11752_neg : (13473649 / 250000000) ≤ -Real.log (947531974519 / 1000000000000) ∧
    -Real.log (947531974519 / 1000000000000) ≤ (53894597 / 1000000000) := by
  have h := checkLog_sound (w := (52468025481 / 1947531974519)) (n := 12)
    (lo := (13473649 / 250000000)) (hi := (53894597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 947531974519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 947531974519) = 1/(947531974519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11752 : Bounds (-53894597 / 1000000000) (-13473649 / 250000000) (Real.log (947531974519 / 1000000000000)) := by
  have h := reflection_log_11752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11753_neg : (116598067 / 250000000) ≤ -Real.log (250000000000 / 398558060863) ∧
    -Real.log (250000000000 / 398558060863) ≤ (466392269 / 1000000000) := by
  have h := checkLog_sound (w := (148558060863 / 648558060863)) (n := 12)
    (lo := (116598067 / 250000000)) (hi := (466392269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398558060863 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398558060863 / 250000000000) = 1/(250000000000 / 398558060863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11753 : Bounds (116598067 / 250000000) (466392269 / 1000000000) (Real.log (398558060863 / 250000000000)) := by
  have h := reflection_log_11753_neg
  have he : Real.log (398558060863 / 250000000000) = -Real.log (250000000000 / 398558060863) := by
    rw [show ((398558060863 / 250000000000) : ℝ) = ((250000000000 / 398558060863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11754_neg : (468471849 / 1000000000) ≤ -Real.log (100000000000 / 159755102889) ∧
    -Real.log (100000000000 / 159755102889) ≤ (9369437 / 20000000) := by
  have h := checkLog_sound (w := (59755102889 / 259755102889)) (n := 12)
    (lo := (468471849 / 1000000000)) (hi := (9369437 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159755102889 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159755102889 / 100000000000) = 1/(100000000000 / 159755102889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11754 : Bounds (468471849 / 1000000000) (9369437 / 20000000) (Real.log (159755102889 / 100000000000)) := by
  have h := reflection_log_11754_neg
  have he : Real.log (159755102889 / 100000000000) = -Real.log (100000000000 / 159755102889) := by
    rw [show ((159755102889 / 100000000000) : ℝ) = ((100000000000 / 159755102889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11755_neg : (474713677 / 500000000) ≤ -Real.log (25000000000 / 64605734767) ∧
    -Real.log (25000000000 / 64605734767) ≤ (237356839 / 250000000) := by
  have h := checkLog_sound (w := (14605734767 / 114605734767)) (n := 12)
    (lo := (128140087 / 500000000)) (hi := (10251207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64605734767 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64605734767 / 50000000000) = 1/(25000000000 / 64605734767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11755 : Bounds (474713677 / 500000000) (237356839 / 250000000) (Real.log (64605734767 / 25000000000)) := by
  have h := reflection_log_11755_neg
  have he : Real.log (64605734767 / 25000000000) = -Real.log (25000000000 / 64605734767) := by
    rw [show ((64605734767 / 25000000000) : ℝ) = ((25000000000 / 64605734767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11756_neg : (475957159 / 500000000) ≤ -Real.log (250000000000 / 647666068223) ∧
    -Real.log (250000000000 / 647666068223) ≤ (11898929 / 12500000) := by
  have h := checkLog_sound (w := (147666068223 / 1147666068223)) (n := 12)
    (lo := (129383569 / 500000000)) (hi := (258767139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647666068223 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(647666068223 / 500000000000) = 1/(250000000000 / 647666068223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11756 : Bounds (475957159 / 500000000) (11898929 / 12500000) (Real.log (647666068223 / 250000000000)) := by
  have h := reflection_log_11756_neg
  have he : Real.log (647666068223 / 250000000000) = -Real.log (250000000000 / 647666068223) := by
    rw [show ((647666068223 / 250000000000) : ℝ) = ((250000000000 / 647666068223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11757_neg : (4592713 / 12500000) ≤ -Real.log (250 / 361) ∧
    -Real.log (250 / 361) ≤ (367417041 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 611)) (n := 12)
    (lo := (4592713 / 12500000)) (hi := (367417041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361 / 250) = 1/(250 / 361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11757 : Bounds (4592713 / 12500000) (367417041 / 1000000000) (Real.log (361 / 250)) := by
  have h := reflection_log_11757_neg
  have he : Real.log (361 / 250) = -Real.log (250 / 361) := by
    rw [show ((361 / 250) : ℝ) = ((250 / 361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11758_neg : (73373373 / 125000000) ≤ -Real.log (139 / 250) ∧
    -Real.log (139 / 250) ≤ (117397397 / 200000000) := by
  have h := checkLog_sound (w := (111 / 389)) (n := 12)
    (lo := (73373373 / 125000000)) (hi := (117397397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 139) = 1/(139 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11758 : Bounds (-117397397 / 200000000) (-73373373 / 125000000) (Real.log (139 / 250)) := by
  have h := reflection_log_11758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11759_neg : (443901 / 1000000000) ≤ -Real.log (250000 / 250111) ∧
    -Real.log (250000 / 250111) ≤ (221951 / 500000000) := by
  have h := checkLog_sound (w := (111 / 500111)) (n := 12)
    (lo := (443901 / 1000000000)) (hi := (221951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250111 / 250000) = 1/(250000 / 250111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11759 : Bounds (443901 / 1000000000) (221951 / 500000000) (Real.log (250111 / 250000)) := by
  have h := reflection_log_11759_neg
  have he : Real.log (250111 / 250000) = -Real.log (250000 / 250111) := by
    rw [show ((250111 / 250000) : ℝ) = ((250000 / 250111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11760_neg : (222049 / 500000000) ≤ -Real.log (249889 / 250000) ∧
    -Real.log (249889 / 250000) ≤ (444099 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 499889)) (n := 12)
    (lo := (222049 / 500000000)) (hi := (444099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249889) = 1/(249889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11760 : Bounds (-444099 / 1000000000) (-222049 / 500000000) (Real.log (249889 / 250000)) := by
  have h := reflection_log_11760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11761_neg : (3229743 / 15625000) ≤ -Real.log (500000 / 614809) ∧
    -Real.log (500000 / 614809) ≤ (206703553 / 1000000000) := by
  have h := checkLog_sound (w := (114809 / 1114809)) (n := 12)
    (lo := (3229743 / 15625000)) (hi := (206703553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614809 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614809 / 500000) = 1/(500000 / 614809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11761 : Bounds (3229743 / 15625000) (206703553 / 1000000000) (Real.log (614809 / 500000)) := by
  have h := reflection_log_11761_neg
  have he : Real.log (614809 / 500000) = -Real.log (500000 / 614809) := by
    rw [show ((614809 / 500000) : ℝ) = ((500000 / 614809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11762_neg : (260868783 / 1000000000) ≤ -Real.log (385191 / 500000) ∧
    -Real.log (385191 / 500000) ≤ (16304299 / 62500000) := by
  have h := checkLog_sound (w := (114809 / 885191)) (n := 12)
    (lo := (260868783 / 1000000000)) (hi := (16304299 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385191) = 1/(385191 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11762 : Bounds (-16304299 / 62500000) (-260868783 / 1000000000) (Real.log (385191 / 500000)) := by
  have h := reflection_log_11762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11763_neg : (41501021 / 200000000) ≤ -Real.log (250000 / 307651) ∧
    -Real.log (250000 / 307651) ≤ (103752553 / 500000000) := by
  have h := checkLog_sound (w := (57651 / 557651)) (n := 12)
    (lo := (41501021 / 200000000)) (hi := (103752553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307651 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307651 / 250000) = 1/(250000 / 307651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11763 : Bounds (41501021 / 200000000) (103752553 / 500000000) (Real.log (307651 / 250000)) := by
  have h := reflection_log_11763_neg
  have he : Real.log (307651 / 250000) = -Real.log (250000 / 307651) := by
    rw [show ((307651 / 250000) : ℝ) = ((250000 / 307651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11764_neg : (262149487 / 1000000000) ≤ -Real.log (192349 / 250000) ∧
    -Real.log (192349 / 250000) ≤ (16384343 / 62500000) := by
  have h := checkLog_sound (w := (57651 / 442349)) (n := 12)
    (lo := (262149487 / 1000000000)) (hi := (16384343 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192349) = 1/(192349 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11764 : Bounds (-16384343 / 62500000) (-262149487 / 1000000000) (Real.log (192349 / 250000)) := by
  have h := reflection_log_11764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11765_neg : (54644381 / 1000000000) ≤ -Real.log (59176362199 / 62500000000) ∧
    -Real.log (59176362199 / 62500000000) ≤ (27322191 / 500000000) := by
  have h := checkLog_sound (w := (3323637801 / 121676362199)) (n := 12)
    (lo := (54644381 / 1000000000)) (hi := (27322191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59176362199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59176362199) = 1/(59176362199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11765 : Bounds (-27322191 / 500000000) (-54644381 / 1000000000) (Real.log (59176362199 / 62500000000)) := by
  have h := reflection_log_11765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11766_neg : (54165231 / 1000000000) ≤ -Real.log (236818893519 / 250000000000) ∧
    -Real.log (236818893519 / 250000000000) ≤ (3385327 / 62500000) := by
  have h := checkLog_sound (w := (13181106481 / 486818893519)) (n := 12)
    (lo := (54165231 / 1000000000)) (hi := (3385327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236818893519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236818893519) = 1/(236818893519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11766 : Bounds (-3385327 / 62500000) (-54165231 / 1000000000) (Real.log (236818893519 / 250000000000)) := by
  have h := reflection_log_11766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11767_neg : (93514467 / 200000000) ≤ -Real.log (500000000000 / 798057327403) ∧
    -Real.log (500000000000 / 798057327403) ≤ (29223271 / 62500000) := by
  have h := checkLog_sound (w := (298057327403 / 1298057327403)) (n := 12)
    (lo := (93514467 / 200000000)) (hi := (29223271 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798057327403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798057327403 / 500000000000) = 1/(500000000000 / 798057327403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11767 : Bounds (93514467 / 200000000) (29223271 / 62500000) (Real.log (798057327403 / 500000000000)) := by
  have h := reflection_log_11767_neg
  have he : Real.log (798057327403 / 500000000000) = -Real.log (500000000000 / 798057327403) := by
    rw [show ((798057327403 / 500000000000) : ℝ) = ((500000000000 / 798057327403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11768_neg : (469654593 / 1000000000) ≤ -Real.log (1953125000 / 3123909453) ∧
    -Real.log (1953125000 / 3123909453) ≤ (234827297 / 500000000) := by
  have h := checkLog_sound (w := (1170784453 / 5077034453)) (n := 12)
    (lo := (469654593 / 1000000000)) (hi := (234827297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3123909453 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3123909453 / 1953125000) = 1/(1953125000 / 3123909453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11768 : Bounds (469654593 / 1000000000) (234827297 / 500000000) (Real.log (3123909453 / 1953125000)) := by
  have h := reflection_log_11768_neg
  have he : Real.log (3123909453 / 1953125000) = -Real.log (1953125000 / 3123909453) := by
    rw [show ((3123909453 / 1953125000) : ℝ) = ((1953125000 / 3123909453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11769_neg : (475957159 / 500000000) ≤ -Real.log (100000000000 / 259066427289) ∧
    -Real.log (100000000000 / 259066427289) ≤ (11898929 / 12500000) := by
  have h := checkLog_sound (w := (59066427289 / 459066427289)) (n := 12)
    (lo := (129383569 / 500000000)) (hi := (258767139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259066427289 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259066427289 / 200000000000) = 1/(100000000000 / 259066427289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11769 : Bounds (475957159 / 500000000) (11898929 / 12500000) (Real.log (259066427289 / 100000000000)) := by
  have h := reflection_log_11769_neg
  have he : Real.log (259066427289 / 100000000000) = -Real.log (100000000000 / 259066427289) := by
    rw [show ((259066427289 / 100000000000) : ℝ) = ((100000000000 / 259066427289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11770_neg : (119300503 / 125000000) ≤ -Real.log (12500000000 / 32464028777) ∧
    -Real.log (12500000000 / 32464028777) ≤ (477202013 / 500000000) := by
  have h := checkLog_sound (w := (7464028777 / 57464028777)) (n := 12)
    (lo := (65314211 / 250000000)) (hi := (52251369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32464028777 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32464028777 / 25000000000) = 1/(12500000000 / 32464028777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11770 : Bounds (119300503 / 125000000) (477202013 / 500000000) (Real.log (32464028777 / 12500000000)) := by
  have h := reflection_log_11770_neg
  have he : Real.log (32464028777 / 12500000000) = -Real.log (12500000000 / 32464028777) := by
    rw [show ((32464028777 / 12500000000) : ℝ) = ((12500000000 / 32464028777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11771_neg : (368109321 / 1000000000) ≤ -Real.log (200 / 289) ∧
    -Real.log (200 / 289) ≤ (184054661 / 500000000) := by
  have h := checkLog_sound (w := (89 / 489)) (n := 12)
    (lo := (368109321 / 1000000000)) (hi := (184054661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289 / 200) = 1/(200 / 289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11771 : Bounds (368109321 / 1000000000) (184054661 / 500000000) (Real.log (289 / 200)) := by
  have h := reflection_log_11771_neg
  have he : Real.log (289 / 200) = -Real.log (200 / 289) := by
    rw [show ((289 / 200) : ℝ) = ((200 / 289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11772_neg : (117757433 / 200000000) ≤ -Real.log (111 / 200) ∧
    -Real.log (111 / 200) ≤ (294393583 / 500000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 111) = 1/(111 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11772 : Bounds (-294393583 / 500000000) (-117757433 / 200000000) (Real.log (111 / 200)) := by
  have h := reflection_log_11772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11773_neg : (444901 / 1000000000) ≤ -Real.log (200000 / 200089) ∧
    -Real.log (200000 / 200089) ≤ (222451 / 500000000) := by
  have h := checkLog_sound (w := (89 / 400089)) (n := 12)
    (lo := (444901 / 1000000000)) (hi := (222451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200089 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200089 / 200000) = 1/(200000 / 200089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11773 : Bounds (444901 / 1000000000) (222451 / 500000000) (Real.log (200089 / 200000)) := by
  have h := reflection_log_11773_neg
  have he : Real.log (200089 / 200000) = -Real.log (200000 / 200089) := by
    rw [show ((200089 / 200000) : ℝ) = ((200000 / 200089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11774_neg : (445099 / 1000000000) ≤ -Real.log (199911 / 200000) ∧
    -Real.log (199911 / 200000) ≤ (4451 / 10000000) := by
  have h := checkLog_sound (w := (89 / 399911)) (n := 12)
    (lo := (445099 / 1000000000)) (hi := (4451 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199911) = 1/(199911 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11774 : Bounds (-4451 / 10000000) (-445099 / 1000000000) (Real.log (199911 / 200000)) := by
  have h := reflection_log_11774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11775_neg : (404604 / 1953125) ≤ -Real.log (31250 / 38443) ∧
    -Real.log (31250 / 38443) ≤ (207157249 / 1000000000) := by
  have h := checkLog_sound (w := (7193 / 69693)) (n := 12)
    (lo := (404604 / 1953125)) (hi := (207157249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38443 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38443 / 31250) = 1/(31250 / 38443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11775 : Bounds (404604 / 1953125) (207157249 / 1000000000) (Real.log (38443 / 31250)) := by
  have h := reflection_log_11775_neg
  have he : Real.log (38443 / 31250) = -Real.log (31250 / 38443) := by
    rw [show ((38443 / 31250) : ℝ) = ((31250 / 38443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


