-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:41:51.314138+00:00
-- url     : https://prove2.me/theorems/a4673020-fab8-4411-bcab-3b47e6936e42
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0083 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0084, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0085) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5376_neg : (94341 / 500000000) ≤ -Real.log (10000000 / 10001887) ∧
    -Real.log (10000000 / 10001887) ≤ (188683 / 1000000000) := by
  have h := checkLog_sound (w := (1887 / 20001887)) (n := 12)
    (lo := (94341 / 500000000)) (hi := (188683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001887 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001887 / 10000000) = 1/(10000000 / 10001887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5376 : Bounds (94341 / 500000000) (188683 / 1000000000) (Real.log (10001887 / 10000000)) := by
  have h := reflection_log_5376_neg
  have he : Real.log (10001887 / 10000000) = -Real.log (10000000 / 10001887) := by
    rw [show ((10001887 / 10000000) : ℝ) = ((10000000 / 10001887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5377_neg : (188717 / 1000000000) ≤ -Real.log (9998113 / 10000000) ∧
    -Real.log (9998113 / 10000000) ≤ (94359 / 500000000) := by
  have h := checkLog_sound (w := (1887 / 19998113)) (n := 12)
    (lo := (188717 / 1000000000)) (hi := (94359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998113) = 1/(9998113 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5377 : Bounds (-94359 / 500000000) (-188717 / 1000000000) (Real.log (9998113 / 10000000)) := by
  have h := reflection_log_5377_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5378_neg : (45293613 / 500000000) ≤ -Real.log (1000000 / 1094817) ∧
    -Real.log (1000000 / 1094817) ≤ (90587227 / 1000000000) := by
  have h := checkLog_sound (w := (94817 / 2094817)) (n := 12)
    (lo := (45293613 / 500000000)) (hi := (90587227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094817 / 1000000) = 1/(1000000 / 1094817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5378 : Bounds (45293613 / 500000000) (90587227 / 1000000000) (Real.log (1094817 / 1000000)) := by
  have h := reflection_log_5378_neg
  have he : Real.log (1094817 / 1000000) = -Real.log (1000000 / 1094817) := by
    rw [show ((1094817 / 1000000) : ℝ) = ((1000000 / 1094817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5379_neg : (19923629 / 200000000) ≤ -Real.log (905183 / 1000000) ∧
    -Real.log (905183 / 1000000) ≤ (49809073 / 500000000) := by
  have h := checkLog_sound (w := (94817 / 1905183)) (n := 12)
    (lo := (19923629 / 200000000)) (hi := (49809073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905183) = 1/(905183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5379 : Bounds (-49809073 / 500000000) (-19923629 / 200000000) (Real.log (905183 / 1000000)) := by
  have h := reflection_log_5379_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5380_neg : (90805503 / 1000000000) ≤ -Real.log (62500 / 68441) ∧
    -Real.log (62500 / 68441) ≤ (354709 / 3906250) := by
  have h := checkLog_sound (w := (5941 / 130941)) (n := 12)
    (lo := (90805503 / 1000000000)) (hi := (354709 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68441 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68441 / 62500) = 1/(62500 / 68441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5380 : Bounds (90805503 / 1000000000) (354709 / 3906250) (Real.log (68441 / 62500)) := by
  have h := reflection_log_5380_neg
  have he : Real.log (68441 / 62500) = -Real.log (62500 / 68441) := by
    rw [show ((68441 / 62500) : ℝ) = ((62500 / 68441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5381_neg : (19976443 / 200000000) ≤ -Real.log (56559 / 62500) ∧
    -Real.log (56559 / 62500) ≤ (12485277 / 125000000) := by
  have h := checkLog_sound (w := (5941 / 119059)) (n := 12)
    (lo := (19976443 / 200000000)) (hi := (12485277 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56559) = 1/(56559 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5381 : Bounds (-12485277 / 125000000) (-19976443 / 200000000) (Real.log (56559 / 62500)) := by
  have h := reflection_log_5381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5382_neg : (1134589 / 125000000) ≤ -Real.log (3870954519 / 3906250000) ∧
    -Real.log (3870954519 / 3906250000) ≤ (9076713 / 1000000000) := by
  have h := checkLog_sound (w := (35295481 / 7777204519)) (n := 12)
    (lo := (1134589 / 125000000)) (hi := (9076713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3870954519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3870954519) = 1/(3870954519 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5382 : Bounds (-9076713 / 1000000000) (-1134589 / 125000000) (Real.log (3870954519 / 3906250000)) := by
  have h := reflection_log_5382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5383_neg : (9030919 / 1000000000) ≤ -Real.log (991009736511 / 1000000000000) ∧
    -Real.log (991009736511 / 1000000000000) ≤ (225773 / 25000000) := by
  have h := checkLog_sound (w := (8990263489 / 1991009736511)) (n := 12)
    (lo := (9030919 / 1000000000)) (hi := (225773 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991009736511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991009736511) = 1/(991009736511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5383 : Bounds (-225773 / 25000000) (-9030919 / 1000000000) (Real.log (991009736511 / 1000000000000)) := by
  have h := reflection_log_5383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5384_neg : (190205371 / 1000000000) ≤ -Real.log (500000000000 / 604748984459) ∧
    -Real.log (500000000000 / 604748984459) ≤ (47551343 / 250000000) := by
  have h := checkLog_sound (w := (104748984459 / 1104748984459)) (n := 12)
    (lo := (190205371 / 1000000000)) (hi := (47551343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604748984459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604748984459 / 500000000000) = 1/(500000000000 / 604748984459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5384 : Bounds (190205371 / 1000000000) (47551343 / 250000000) (Real.log (604748984459 / 500000000000)) := by
  have h := reflection_log_5384_neg
  have he : Real.log (604748984459 / 500000000000) = -Real.log (500000000000 / 604748984459) := by
    rw [show ((604748984459 / 500000000000) : ℝ) = ((500000000000 / 604748984459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5385_neg : (190687719 / 1000000000) ≤ -Real.log (31250000000 / 37815047119) ∧
    -Real.log (31250000000 / 37815047119) ≤ (4767193 / 25000000) := by
  have h := checkLog_sound (w := (6565047119 / 69065047119)) (n := 12)
    (lo := (190687719 / 1000000000)) (hi := (4767193 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37815047119 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37815047119 / 31250000000) = 1/(31250000000 / 37815047119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5385 : Bounds (190687719 / 1000000000) (4767193 / 25000000) (Real.log (37815047119 / 31250000000)) := by
  have h := reflection_log_5385_neg
  have he : Real.log (37815047119 / 31250000000) = -Real.log (31250000000 / 37815047119) := by
    rw [show ((37815047119 / 31250000000) : ℝ) = ((31250000000 / 37815047119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5386_neg : (11930321 / 31250000) ≤ -Real.log (500000000000 / 732437761893) ∧
    -Real.log (500000000000 / 732437761893) ≤ (381770273 / 1000000000) := by
  have h := checkLog_sound (w := (232437761893 / 1232437761893)) (n := 12)
    (lo := (11930321 / 31250000)) (hi := (381770273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732437761893 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732437761893 / 500000000000) = 1/(500000000000 / 732437761893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5386 : Bounds (11930321 / 31250000) (381770273 / 1000000000) (Real.log (732437761893 / 500000000000)) := by
  have h := reflection_log_5386_neg
  have he : Real.log (732437761893 / 500000000000) = -Real.log (500000000000 / 732437761893) := by
    rw [show ((732437761893 / 500000000000) : ℝ) = ((500000000000 / 732437761893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5387_neg : (95494413 / 250000000) ≤ -Real.log (500000000000 / 732589670899) ∧
    -Real.log (500000000000 / 732589670899) ≤ (381977653 / 1000000000) := by
  have h := checkLog_sound (w := (232589670899 / 1232589670899)) (n := 12)
    (lo := (95494413 / 250000000)) (hi := (381977653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732589670899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732589670899 / 500000000000) = 1/(500000000000 / 732589670899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5387 : Bounds (95494413 / 250000000) (381977653 / 1000000000) (Real.log (732589670899 / 500000000000)) := by
  have h := reflection_log_5387_neg
  have he : Real.log (732589670899 / 500000000000) = -Real.log (500000000000 / 732589670899) := by
    rw [show ((732589670899 / 500000000000) : ℝ) = ((500000000000 / 732589670899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5388_neg : (86472197 / 500000000) ≤ -Real.log (625 / 743) ∧
    -Real.log (625 / 743) ≤ (34588879 / 200000000) := by
  have h := checkLog_sound (w := (59 / 684)) (n := 12)
    (lo := (86472197 / 500000000)) (hi := (34588879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743 / 625) = 1/(625 / 743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5388 : Bounds (86472197 / 500000000) (34588879 / 200000000) (Real.log (743 / 625)) := by
  have h := reflection_log_5388_neg
  have he : Real.log (743 / 625) = -Real.log (625 / 743) := by
    rw [show ((743 / 625) : ℝ) = ((625 / 743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5389_neg : (104620323 / 500000000) ≤ -Real.log (507 / 625) ∧
    -Real.log (507 / 625) ≤ (209240647 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 566)) (n := 12)
    (lo := (104620323 / 500000000)) (hi := (209240647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 507) = 1/(507 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5389 : Bounds (-209240647 / 1000000000) (-104620323 / 500000000) (Real.log (507 / 625)) := by
  have h := reflection_log_5389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5390_neg : (94391 / 500000000) ≤ -Real.log (312500 / 312559) ∧
    -Real.log (312500 / 312559) ≤ (188783 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 625059)) (n := 12)
    (lo := (94391 / 500000000)) (hi := (188783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312559 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312559 / 312500) = 1/(312500 / 312559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5390 : Bounds (94391 / 500000000) (188783 / 1000000000) (Real.log (312559 / 312500)) := by
  have h := reflection_log_5390_neg
  have he : Real.log (312559 / 312500) = -Real.log (312500 / 312559) := by
    rw [show ((312559 / 312500) : ℝ) = ((312500 / 312559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5391_neg : (188817 / 1000000000) ≤ -Real.log (312441 / 312500) ∧
    -Real.log (312441 / 312500) ≤ (94409 / 500000000) := by
  have h := checkLog_sound (w := (59 / 624941)) (n := 12)
    (lo := (188817 / 1000000000)) (hi := (94409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312441) = 1/(312441 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5391 : Bounds (-94409 / 500000000) (-188817 / 1000000000) (Real.log (312441 / 312500)) := by
  have h := reflection_log_5391_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5392_neg : (5664613 / 62500000) ≤ -Real.log (250000 / 273717) ∧
    -Real.log (250000 / 273717) ≤ (90633809 / 1000000000) := by
  have h := checkLog_sound (w := (23717 / 523717)) (n := 12)
    (lo := (5664613 / 62500000)) (hi := (90633809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273717 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273717 / 250000) = 1/(250000 / 273717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5392 : Bounds (5664613 / 62500000) (90633809 / 1000000000) (Real.log (273717 / 250000)) := by
  have h := reflection_log_5392_neg
  have he : Real.log (273717 / 250000) = -Real.log (250000 / 273717) := by
    rw [show ((273717 / 250000) : ℝ) = ((250000 / 273717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5393_neg : (99674489 / 1000000000) ≤ -Real.log (226283 / 250000) ∧
    -Real.log (226283 / 250000) ≤ (9967449 / 100000000) := by
  have h := checkLog_sound (w := (23717 / 476283)) (n := 12)
    (lo := (99674489 / 1000000000)) (hi := (9967449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226283) = 1/(226283 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5393 : Bounds (-9967449 / 100000000) (-99674489 / 1000000000) (Real.log (226283 / 250000)) := by
  have h := reflection_log_5393_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5394_neg : (22713247 / 250000000) ≤ -Real.log (250000 / 273777) ∧
    -Real.log (250000 / 273777) ≤ (90852989 / 1000000000) := by
  have h := checkLog_sound (w := (23777 / 523777)) (n := 12)
    (lo := (22713247 / 250000000)) (hi := (90852989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273777 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273777 / 250000) = 1/(250000 / 273777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5394 : Bounds (22713247 / 250000000) (90852989 / 1000000000) (Real.log (273777 / 250000)) := by
  have h := reflection_log_5394_neg
  have he : Real.log (273777 / 250000) = -Real.log (250000 / 273777) := by
    rw [show ((273777 / 250000) : ℝ) = ((250000 / 273777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5395_neg : (99939679 / 1000000000) ≤ -Real.log (226223 / 250000) ∧
    -Real.log (226223 / 250000) ≤ (624623 / 6250000) := by
  have h := checkLog_sound (w := (23777 / 476223)) (n := 12)
    (lo := (99939679 / 1000000000)) (hi := (624623 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226223) = 1/(226223 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5395 : Bounds (-624623 / 6250000) (-99939679 / 1000000000) (Real.log (226223 / 250000)) := by
  have h := reflection_log_5395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5396_neg : (908669 / 100000000) ≤ -Real.log (61934654271 / 62500000000) ∧
    -Real.log (61934654271 / 62500000000) ≤ (9086691 / 1000000000) := by
  have h := checkLog_sound (w := (565345729 / 124434654271)) (n := 12)
    (lo := (908669 / 100000000)) (hi := (9086691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61934654271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61934654271) = 1/(61934654271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5396 : Bounds (-9086691 / 1000000000) (-908669 / 100000000) (Real.log (61934654271 / 62500000000)) := by
  have h := reflection_log_5396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5397_neg : (9040681 / 1000000000) ≤ -Real.log (61937503911 / 62500000000) ∧
    -Real.log (61937503911 / 62500000000) ≤ (4520341 / 500000000) := by
  have h := checkLog_sound (w := (562496089 / 124437503911)) (n := 12)
    (lo := (9040681 / 1000000000)) (hi := (4520341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61937503911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61937503911) = 1/(61937503911 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5397 : Bounds (-4520341 / 500000000) (-9040681 / 1000000000) (Real.log (61937503911 / 62500000000)) := by
  have h := reflection_log_5397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5398_neg : (190308297 / 1000000000) ≤ -Real.log (31250000000 / 37800701997) ∧
    -Real.log (31250000000 / 37800701997) ≤ (95154149 / 500000000) := by
  have h := checkLog_sound (w := (6550701997 / 69050701997)) (n := 12)
    (lo := (190308297 / 1000000000)) (hi := (95154149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37800701997 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37800701997 / 31250000000) = 1/(31250000000 / 37800701997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5398 : Bounds (190308297 / 1000000000) (95154149 / 500000000) (Real.log (37800701997 / 31250000000)) := by
  have h := reflection_log_5398_neg
  have he : Real.log (37800701997 / 31250000000) = -Real.log (31250000000 / 37800701997) := by
    rw [show ((37800701997 / 31250000000) : ℝ) = ((31250000000 / 37800701997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5399_neg : (190792667 / 1000000000) ≤ -Real.log (31250000000 / 37819015971) ∧
    -Real.log (31250000000 / 37819015971) ≤ (47698167 / 250000000) := by
  have h := checkLog_sound (w := (6569015971 / 69069015971)) (n := 12)
    (lo := (190792667 / 1000000000)) (hi := (47698167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37819015971 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37819015971 / 31250000000) = 1/(31250000000 / 37819015971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5399 : Bounds (190792667 / 1000000000) (47698167 / 250000000) (Real.log (37819015971 / 31250000000)) := by
  have h := reflection_log_5399_neg
  have he : Real.log (37819015971 / 31250000000) = -Real.log (31250000000 / 37819015971) := by
    rw [show ((37819015971 / 31250000000) : ℝ) = ((31250000000 / 37819015971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5400_neg : (95494413 / 250000000) ≤ -Real.log (250000000000 / 366294835449) ∧
    -Real.log (250000000000 / 366294835449) ≤ (381977653 / 1000000000) := by
  have h := checkLog_sound (w := (116294835449 / 616294835449)) (n := 12)
    (lo := (95494413 / 250000000)) (hi := (381977653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366294835449 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366294835449 / 250000000000) = 1/(250000000000 / 366294835449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5400 : Bounds (95494413 / 250000000) (381977653 / 1000000000) (Real.log (366294835449 / 250000000000)) := by
  have h := reflection_log_5400_neg
  have he : Real.log (366294835449 / 250000000000) = -Real.log (250000000000 / 366294835449) := by
    rw [show ((366294835449 / 250000000000) : ℝ) = ((250000000000 / 366294835449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5401_neg : (382185041 / 1000000000) ≤ -Real.log (250000000000 / 366370808679) ∧
    -Real.log (250000000000 / 366370808679) ≤ (191092521 / 500000000) := by
  have h := checkLog_sound (w := (116370808679 / 616370808679)) (n := 12)
    (lo := (382185041 / 1000000000)) (hi := (191092521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366370808679 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366370808679 / 250000000000) = 1/(250000000000 / 366370808679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5401 : Bounds (382185041 / 1000000000) (191092521 / 500000000) (Real.log (366370808679 / 250000000000)) := by
  have h := reflection_log_5401_neg
  have he : Real.log (366370808679 / 250000000000) = -Real.log (250000000000 / 366370808679) := by
    rw [show ((366370808679 / 250000000000) : ℝ) = ((250000000000 / 366370808679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5402_neg : (173028509 / 1000000000) ≤ -Real.log (10000 / 11889) ∧
    -Real.log (10000 / 11889) ≤ (17302851 / 100000000) := by
  have h := checkLog_sound (w := (1889 / 21889)) (n := 12)
    (lo := (173028509 / 1000000000)) (hi := (17302851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11889 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11889 / 10000) = 1/(10000 / 11889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5402 : Bounds (173028509 / 1000000000) (17302851 / 100000000) (Real.log (11889 / 10000)) := by
  have h := reflection_log_5402_neg
  have he : Real.log (11889 / 10000) = -Real.log (10000 / 11889) := by
    rw [show ((11889 / 10000) : ℝ) = ((10000 / 11889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5403_neg : (209363927 / 1000000000) ≤ -Real.log (8111 / 10000) ∧
    -Real.log (8111 / 10000) ≤ (26170491 / 125000000) := by
  have h := checkLog_sound (w := (1889 / 18111)) (n := 12)
    (lo := (209363927 / 1000000000)) (hi := (26170491 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8111) = 1/(8111 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5403 : Bounds (-26170491 / 125000000) (-209363927 / 1000000000) (Real.log (8111 / 10000)) := by
  have h := reflection_log_5403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5404_neg : (94441 / 500000000) ≤ -Real.log (10000000 / 10001889) ∧
    -Real.log (10000000 / 10001889) ≤ (188883 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 20001889)) (n := 12)
    (lo := (94441 / 500000000)) (hi := (188883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001889 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001889 / 10000000) = 1/(10000000 / 10001889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5404 : Bounds (94441 / 500000000) (188883 / 1000000000) (Real.log (10001889 / 10000000)) := by
  have h := reflection_log_5404_neg
  have he : Real.log (10001889 / 10000000) = -Real.log (10000000 / 10001889) := by
    rw [show ((10001889 / 10000000) : ℝ) = ((10000000 / 10001889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5405_neg : (188917 / 1000000000) ≤ -Real.log (9998111 / 10000000) ∧
    -Real.log (9998111 / 10000000) ≤ (94459 / 500000000) := by
  have h := checkLog_sound (w := (1889 / 19998111)) (n := 12)
    (lo := (188917 / 1000000000)) (hi := (94459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998111) = 1/(9998111 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5405 : Bounds (-94459 / 500000000) (-188917 / 1000000000) (Real.log (9998111 / 10000000)) := by
  have h := reflection_log_5405_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5406_neg : (90680387 / 1000000000) ≤ -Real.log (1000000 / 1094919) ∧
    -Real.log (1000000 / 1094919) ≤ (22670097 / 250000000) := by
  have h := checkLog_sound (w := (94919 / 2094919)) (n := 12)
    (lo := (90680387 / 1000000000)) (hi := (22670097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094919 / 1000000) = 1/(1000000 / 1094919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5406 : Bounds (90680387 / 1000000000) (22670097 / 250000000) (Real.log (1094919 / 1000000)) := by
  have h := reflection_log_5406_neg
  have he : Real.log (1094919 / 1000000) = -Real.log (1000000 / 1094919) := by
    rw [show ((1094919 / 1000000) : ℝ) = ((1000000 / 1094919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5407_neg : (24932709 / 250000000) ≤ -Real.log (905081 / 1000000) ∧
    -Real.log (905081 / 1000000) ≤ (99730837 / 1000000000) := by
  have h := checkLog_sound (w := (94919 / 1905081)) (n := 12)
    (lo := (24932709 / 250000000)) (hi := (99730837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905081) = 1/(905081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5407 : Bounds (-99730837 / 1000000000) (-24932709 / 250000000) (Real.log (905081 / 1000000)) := by
  have h := reflection_log_5407_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5408_neg : (45449779 / 500000000) ≤ -Real.log (1000000 / 1095159) ∧
    -Real.log (1000000 / 1095159) ≤ (90899559 / 1000000000) := by
  have h := checkLog_sound (w := (95159 / 2095159)) (n := 12)
    (lo := (45449779 / 500000000)) (hi := (90899559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095159 / 1000000) = 1/(1000000 / 1095159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5408 : Bounds (45449779 / 500000000) (90899559 / 1000000000) (Real.log (1095159 / 1000000)) := by
  have h := reflection_log_5408_neg
  have he : Real.log (1095159 / 1000000) = -Real.log (1000000 / 1095159) := by
    rw [show ((1095159 / 1000000) : ℝ) = ((1000000 / 1095159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5409_neg : (99996041 / 1000000000) ≤ -Real.log (904841 / 1000000) ∧
    -Real.log (904841 / 1000000) ≤ (49998021 / 500000000) := by
  have h := checkLog_sound (w := (95159 / 1904841)) (n := 12)
    (lo := (99996041 / 1000000000)) (hi := (49998021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904841) = 1/(904841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5409 : Bounds (-49998021 / 500000000) (-99996041 / 1000000000) (Real.log (904841 / 1000000)) := by
  have h := reflection_log_5409_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5410_neg : (9096483 / 1000000000) ≤ -Real.log (990944764719 / 1000000000000) ∧
    -Real.log (990944764719 / 1000000000000) ≤ (2274121 / 250000000) := by
  have h := checkLog_sound (w := (9055235281 / 1990944764719)) (n := 12)
    (lo := (9096483 / 1000000000)) (hi := (2274121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990944764719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990944764719) = 1/(990944764719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5410 : Bounds (-2274121 / 250000000) (-9096483 / 1000000000) (Real.log (990944764719 / 1000000000000)) := by
  have h := reflection_log_5410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5411_neg : (565653 / 62500000) ≤ -Real.log (990990383439 / 1000000000000) ∧
    -Real.log (990990383439 / 1000000000000) ≤ (9050449 / 1000000000) := by
  have h := checkLog_sound (w := (9009616561 / 1990990383439)) (n := 12)
    (lo := (565653 / 62500000)) (hi := (9050449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990990383439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990990383439) = 1/(990990383439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5411 : Bounds (-9050449 / 1000000000) (-565653 / 62500000) (Real.log (990990383439 / 1000000000000)) := by
  have h := reflection_log_5411_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5412_neg : (23801403 / 125000000) ≤ -Real.log (500000000000 / 604873486461) ∧
    -Real.log (500000000000 / 604873486461) ≤ (7616449 / 40000000) := by
  have h := checkLog_sound (w := (104873486461 / 1104873486461)) (n := 12)
    (lo := (23801403 / 125000000)) (hi := (7616449 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604873486461 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604873486461 / 500000000000) = 1/(500000000000 / 604873486461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5412 : Bounds (23801403 / 125000000) (7616449 / 40000000) (Real.log (604873486461 / 500000000000)) := by
  have h := reflection_log_5412_neg
  have he : Real.log (604873486461 / 500000000000) = -Real.log (500000000000 / 604873486461) := by
    rw [show ((604873486461 / 500000000000) : ℝ) = ((500000000000 / 604873486461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5413_neg : (190895599 / 1000000000) ≤ -Real.log (500000000000 / 605166543073) ∧
    -Real.log (500000000000 / 605166543073) ≤ (477239 / 2500000) := by
  have h := checkLog_sound (w := (105166543073 / 1105166543073)) (n := 12)
    (lo := (190895599 / 1000000000)) (hi := (477239 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605166543073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605166543073 / 500000000000) = 1/(500000000000 / 605166543073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5413 : Bounds (190895599 / 1000000000) (477239 / 2500000) (Real.log (605166543073 / 500000000000)) := by
  have h := reflection_log_5413_neg
  have he : Real.log (605166543073 / 500000000000) = -Real.log (500000000000 / 605166543073) := by
    rw [show ((605166543073 / 500000000000) : ℝ) = ((500000000000 / 605166543073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5414_neg : (382185041 / 1000000000) ≤ -Real.log (500000000000 / 732741617357) ∧
    -Real.log (500000000000 / 732741617357) ≤ (191092521 / 500000000) := by
  have h := checkLog_sound (w := (232741617357 / 1232741617357)) (n := 12)
    (lo := (382185041 / 1000000000)) (hi := (191092521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732741617357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732741617357 / 500000000000) = 1/(500000000000 / 732741617357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5414 : Bounds (382185041 / 1000000000) (191092521 / 500000000) (Real.log (732741617357 / 500000000000)) := by
  have h := reflection_log_5414_neg
  have he : Real.log (732741617357 / 500000000000) = -Real.log (500000000000 / 732741617357) := by
    rw [show ((732741617357 / 500000000000) : ℝ) = ((500000000000 / 732741617357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5415_neg : (382392437 / 1000000000) ≤ -Real.log (500000000000 / 732893601283) ∧
    -Real.log (500000000000 / 732893601283) ≤ (191196219 / 500000000) := by
  have h := checkLog_sound (w := (232893601283 / 1232893601283)) (n := 12)
    (lo := (382392437 / 1000000000)) (hi := (191196219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732893601283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732893601283 / 500000000000) = 1/(500000000000 / 732893601283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5415 : Bounds (382392437 / 1000000000) (191196219 / 500000000) (Real.log (732893601283 / 500000000000)) := by
  have h := reflection_log_5415_neg
  have he : Real.log (732893601283 / 500000000000) = -Real.log (500000000000 / 732893601283) := by
    rw [show ((732893601283 / 500000000000) : ℝ) = ((500000000000 / 732893601283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5416_neg : (173112617 / 1000000000) ≤ -Real.log (1000 / 1189) ∧
    -Real.log (1000 / 1189) ≤ (86556309 / 500000000) := by
  have h := checkLog_sound (w := (189 / 2189)) (n := 12)
    (lo := (173112617 / 1000000000)) (hi := (86556309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189 / 1000) = 1/(1000 / 1189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5416 : Bounds (173112617 / 1000000000) (86556309 / 500000000) (Real.log (1189 / 1000)) := by
  have h := reflection_log_5416_neg
  have he : Real.log (1189 / 1000) = -Real.log (1000 / 1189) := by
    rw [show ((1189 / 1000) : ℝ) = ((1000 / 1189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5417_neg : (26185903 / 125000000) ≤ -Real.log (811 / 1000) ∧
    -Real.log (811 / 1000) ≤ (8379489 / 40000000) := by
  have h := checkLog_sound (w := (189 / 1811)) (n := 12)
    (lo := (26185903 / 125000000)) (hi := (8379489 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 811) = 1/(811 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5417 : Bounds (-8379489 / 40000000) (-26185903 / 125000000) (Real.log (811 / 1000)) := by
  have h := reflection_log_5417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5418_neg : (94491 / 500000000) ≤ -Real.log (1000000 / 1000189) ∧
    -Real.log (1000000 / 1000189) ≤ (188983 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 2000189)) (n := 12)
    (lo := (94491 / 500000000)) (hi := (188983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000189 / 1000000) = 1/(1000000 / 1000189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5418 : Bounds (94491 / 500000000) (188983 / 1000000000) (Real.log (1000189 / 1000000)) := by
  have h := reflection_log_5418_neg
  have he : Real.log (1000189 / 1000000) = -Real.log (1000000 / 1000189) := by
    rw [show ((1000189 / 1000000) : ℝ) = ((1000000 / 1000189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5419_neg : (189017 / 1000000000) ≤ -Real.log (999811 / 1000000) ∧
    -Real.log (999811 / 1000000) ≤ (94509 / 500000000) := by
  have h := checkLog_sound (w := (189 / 1999811)) (n := 12)
    (lo := (189017 / 1000000000)) (hi := (94509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999811) = 1/(999811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5419 : Bounds (-94509 / 500000000) (-189017 / 1000000000) (Real.log (999811 / 1000000)) := by
  have h := reflection_log_5419_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5420_neg : (18145393 / 200000000) ≤ -Real.log (100000 / 109497) ∧
    -Real.log (100000 / 109497) ≤ (45363483 / 500000000) := by
  have h := checkLog_sound (w := (9497 / 209497)) (n := 12)
    (lo := (18145393 / 200000000)) (hi := (45363483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109497 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109497 / 100000) = 1/(100000 / 109497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5420 : Bounds (18145393 / 200000000) (45363483 / 500000000) (Real.log (109497 / 100000)) := by
  have h := reflection_log_5420_neg
  have he : Real.log (109497 / 100000) = -Real.log (100000 / 109497) := by
    rw [show ((109497 / 100000) : ℝ) = ((100000 / 109497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5421_neg : (49893593 / 500000000) ≤ -Real.log (90503 / 100000) ∧
    -Real.log (90503 / 100000) ≤ (99787187 / 1000000000) := by
  have h := checkLog_sound (w := (9497 / 190503)) (n := 12)
    (lo := (49893593 / 500000000)) (hi := (99787187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90503) = 1/(90503 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5421 : Bounds (-99787187 / 1000000000) (-49893593 / 500000000) (Real.log (90503 / 100000)) := by
  have h := reflection_log_5421_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5422_neg : (727569 / 8000000) ≤ -Real.log (100000 / 109521) ∧
    -Real.log (100000 / 109521) ≤ (45473063 / 500000000) := by
  have h := checkLog_sound (w := (9521 / 209521)) (n := 12)
    (lo := (727569 / 8000000)) (hi := (45473063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109521 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109521 / 100000) = 1/(100000 / 109521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5422 : Bounds (727569 / 8000000) (45473063 / 500000000) (Real.log (109521 / 100000)) := by
  have h := reflection_log_5422_neg
  have he : Real.log (109521 / 100000) = -Real.log (100000 / 109521) := by
    rw [show ((109521 / 100000) : ℝ) = ((100000 / 109521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5423_neg : (50026203 / 500000000) ≤ -Real.log (90479 / 100000) ∧
    -Real.log (90479 / 100000) ≤ (100052407 / 1000000000) := by
  have h := checkLog_sound (w := (9521 / 190479)) (n := 12)
    (lo := (50026203 / 500000000)) (hi := (100052407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90479) = 1/(90479 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5423 : Bounds (-100052407 / 1000000000) (-50026203 / 500000000) (Real.log (90479 / 100000)) := by
  have h := reflection_log_5423_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5424_neg : (227657 / 25000000) ≤ -Real.log (9909350559 / 10000000000) ∧
    -Real.log (9909350559 / 10000000000) ≤ (9106281 / 1000000000) := by
  have h := checkLog_sound (w := (90649441 / 19909350559)) (n := 12)
    (lo := (227657 / 25000000)) (hi := (9106281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9909350559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9909350559) = 1/(9909350559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5424 : Bounds (-9106281 / 1000000000) (-227657 / 25000000) (Real.log (9909350559 / 10000000000)) := by
  have h := reflection_log_5424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5425_neg : (9060221 / 1000000000) ≤ -Real.log (9909806991 / 10000000000) ∧
    -Real.log (9909806991 / 10000000000) ≤ (4530111 / 500000000) := by
  have h := checkLog_sound (w := (90193009 / 19909806991)) (n := 12)
    (lo := (9060221 / 1000000000)) (hi := (4530111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9909806991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9909806991) = 1/(9909806991 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5425 : Bounds (-4530111 / 500000000) (-9060221 / 1000000000) (Real.log (9909806991 / 10000000000)) := by
  have h := reflection_log_5425_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5426_neg : (23814269 / 125000000) ≤ -Real.log (250000000000 / 302467873993) ∧
    -Real.log (250000000000 / 302467873993) ≤ (190514153 / 1000000000) := by
  have h := checkLog_sound (w := (52467873993 / 552467873993)) (n := 12)
    (lo := (23814269 / 125000000)) (hi := (190514153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302467873993 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302467873993 / 250000000000) = 1/(250000000000 / 302467873993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5426 : Bounds (23814269 / 125000000) (190514153 / 1000000000) (Real.log (302467873993 / 250000000000)) := by
  have h := reflection_log_5426_neg
  have he : Real.log (302467873993 / 250000000000) = -Real.log (250000000000 / 302467873993) := by
    rw [show ((302467873993 / 250000000000) : ℝ) = ((250000000000 / 302467873993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5427_neg : (47749633 / 250000000) ≤ -Real.log (500000000000 / 605228837631) ∧
    -Real.log (500000000000 / 605228837631) ≤ (190998533 / 1000000000) := by
  have h := checkLog_sound (w := (105228837631 / 1105228837631)) (n := 12)
    (lo := (47749633 / 250000000)) (hi := (190998533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605228837631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605228837631 / 500000000000) = 1/(500000000000 / 605228837631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5427 : Bounds (47749633 / 250000000) (190998533 / 1000000000) (Real.log (605228837631 / 500000000000)) := by
  have h := reflection_log_5427_neg
  have he : Real.log (605228837631 / 500000000000) = -Real.log (500000000000 / 605228837631) := by
    rw [show ((605228837631 / 500000000000) : ℝ) = ((500000000000 / 605228837631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5428_neg : (382392437 / 1000000000) ≤ -Real.log (250000000000 / 366446800641) ∧
    -Real.log (250000000000 / 366446800641) ≤ (191196219 / 500000000) := by
  have h := checkLog_sound (w := (116446800641 / 616446800641)) (n := 12)
    (lo := (382392437 / 1000000000)) (hi := (191196219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366446800641 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366446800641 / 250000000000) = 1/(250000000000 / 366446800641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5428 : Bounds (382392437 / 1000000000) (191196219 / 500000000) (Real.log (366446800641 / 250000000000)) := by
  have h := reflection_log_5428_neg
  have he : Real.log (366446800641 / 250000000000) = -Real.log (250000000000 / 366446800641) := by
    rw [show ((366446800641 / 250000000000) : ℝ) = ((250000000000 / 366446800641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5429_neg : (191299921 / 500000000) ≤ -Real.log (500000000000 / 733045622689) ∧
    -Real.log (500000000000 / 733045622689) ≤ (382599843 / 1000000000) := by
  have h := checkLog_sound (w := (233045622689 / 1233045622689)) (n := 12)
    (lo := (191299921 / 500000000)) (hi := (382599843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733045622689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733045622689 / 500000000000) = 1/(500000000000 / 733045622689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5429 : Bounds (191299921 / 500000000) (382599843 / 1000000000) (Real.log (733045622689 / 500000000000)) := by
  have h := reflection_log_5429_neg
  have he : Real.log (733045622689 / 500000000000) = -Real.log (500000000000 / 733045622689) := by
    rw [show ((733045622689 / 500000000000) : ℝ) = ((500000000000 / 733045622689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5430_neg : (86598359 / 500000000) ≤ -Real.log (10000 / 11891) ∧
    -Real.log (10000 / 11891) ≤ (173196719 / 1000000000) := by
  have h := checkLog_sound (w := (1891 / 21891)) (n := 12)
    (lo := (86598359 / 500000000)) (hi := (173196719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11891 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11891 / 10000) = 1/(10000 / 11891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5430 : Bounds (86598359 / 500000000) (173196719 / 1000000000) (Real.log (11891 / 10000)) := by
  have h := reflection_log_5430_neg
  have he : Real.log (11891 / 10000) = -Real.log (10000 / 11891) := by
    rw [show ((11891 / 10000) : ℝ) = ((10000 / 11891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5431_neg : (209610537 / 1000000000) ≤ -Real.log (8109 / 10000) ∧
    -Real.log (8109 / 10000) ≤ (104805269 / 500000000) := by
  have h := checkLog_sound (w := (1891 / 18109)) (n := 12)
    (lo := (209610537 / 1000000000)) (hi := (104805269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8109) = 1/(8109 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5431 : Bounds (-104805269 / 500000000) (-209610537 / 1000000000) (Real.log (8109 / 10000)) := by
  have h := reflection_log_5431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5432_neg : (94541 / 500000000) ≤ -Real.log (10000000 / 10001891) ∧
    -Real.log (10000000 / 10001891) ≤ (189083 / 1000000000) := by
  have h := checkLog_sound (w := (1891 / 20001891)) (n := 12)
    (lo := (94541 / 500000000)) (hi := (189083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001891 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001891 / 10000000) = 1/(10000000 / 10001891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5432 : Bounds (94541 / 500000000) (189083 / 1000000000) (Real.log (10001891 / 10000000)) := by
  have h := reflection_log_5432_neg
  have he : Real.log (10001891 / 10000000) = -Real.log (10000000 / 10001891) := by
    rw [show ((10001891 / 10000000) : ℝ) = ((10000000 / 10001891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5433_neg : (189117 / 1000000000) ≤ -Real.log (9998109 / 10000000) ∧
    -Real.log (9998109 / 10000000) ≤ (94559 / 500000000) := by
  have h := checkLog_sound (w := (1891 / 19998109)) (n := 12)
    (lo := (189117 / 1000000000)) (hi := (94559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998109) = 1/(9998109 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5433 : Bounds (-94559 / 500000000) (-189117 / 1000000000) (Real.log (9998109 / 10000000)) := by
  have h := reflection_log_5433_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5434_neg : (90773541 / 1000000000) ≤ -Real.log (1000000 / 1095021) ∧
    -Real.log (1000000 / 1095021) ≤ (45386771 / 500000000) := by
  have h := checkLog_sound (w := (95021 / 2095021)) (n := 12)
    (lo := (90773541 / 1000000000)) (hi := (45386771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095021 / 1000000) = 1/(1000000 / 1095021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5434 : Bounds (90773541 / 1000000000) (45386771 / 500000000) (Real.log (1095021 / 1000000)) := by
  have h := reflection_log_5434_neg
  have he : Real.log (1095021 / 1000000) = -Real.log (1000000 / 1095021) := by
    rw [show ((1095021 / 1000000) : ℝ) = ((1000000 / 1095021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5435_neg : (99843539 / 1000000000) ≤ -Real.log (904979 / 1000000) ∧
    -Real.log (904979 / 1000000) ≤ (4992177 / 50000000) := by
  have h := checkLog_sound (w := (95021 / 1904979)) (n := 12)
    (lo := (99843539 / 1000000000)) (hi := (4992177 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904979) = 1/(904979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5435 : Bounds (-4992177 / 50000000) (-99843539 / 1000000000) (Real.log (904979 / 1000000)) := by
  have h := reflection_log_5435_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5436_neg : (90992691 / 1000000000) ≤ -Real.log (1000000 / 1095261) ∧
    -Real.log (1000000 / 1095261) ≤ (22748173 / 250000000) := by
  have h := checkLog_sound (w := (95261 / 2095261)) (n := 12)
    (lo := (90992691 / 1000000000)) (hi := (22748173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095261 / 1000000) = 1/(1000000 / 1095261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5436 : Bounds (90992691 / 1000000000) (22748173 / 250000000) (Real.log (1095261 / 1000000)) := by
  have h := reflection_log_5436_neg
  have he : Real.log (1095261 / 1000000) = -Real.log (1000000 / 1095261) := by
    rw [show ((1095261 / 1000000) : ℝ) = ((1000000 / 1095261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5437_neg : (50054387 / 500000000) ≤ -Real.log (904739 / 1000000) ∧
    -Real.log (904739 / 1000000) ≤ (4004351 / 40000000) := by
  have h := checkLog_sound (w := (95261 / 1904739)) (n := 12)
    (lo := (50054387 / 500000000)) (hi := (4004351 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904739) = 1/(904739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5437 : Bounds (-4004351 / 40000000) (-50054387 / 500000000) (Real.log (904739 / 1000000)) := by
  have h := reflection_log_5437_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5438_neg : (9116083 / 1000000000) ≤ -Real.log (990925341879 / 1000000000000) ∧
    -Real.log (990925341879 / 1000000000000) ≤ (2279021 / 250000000) := by
  have h := checkLog_sound (w := (9074658121 / 1990925341879)) (n := 12)
    (lo := (9116083 / 1000000000)) (hi := (2279021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990925341879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990925341879) = 1/(990925341879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5438 : Bounds (-2279021 / 250000000) (-9116083 / 1000000000) (Real.log (990925341879 / 1000000000000)) := by
  have h := reflection_log_5438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5439_neg : (4534999 / 500000000) ≤ -Real.log (990971009559 / 1000000000000) ∧
    -Real.log (990971009559 / 1000000000000) ≤ (9069999 / 1000000000) := by
  have h := checkLog_sound (w := (9028990441 / 1990971009559)) (n := 12)
    (lo := (4534999 / 500000000)) (hi := (9069999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990971009559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990971009559) = 1/(990971009559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5439 : Bounds (-9069999 / 1000000000) (-4534999 / 500000000) (Real.log (990971009559 / 1000000000000)) := by
  have h := reflection_log_5439_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


