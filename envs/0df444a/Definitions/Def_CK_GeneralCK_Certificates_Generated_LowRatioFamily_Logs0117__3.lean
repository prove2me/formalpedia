-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0117__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0117__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:51:58.841811+00:00
-- url     : https://prove2.me/theorems/c1f7e884-9bca-4b57-823f-a49d65982129
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0117 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0118, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0117 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0118, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0119)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0117 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0118, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0119)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0117 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0118, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0119) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0117 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0118, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0119).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0117 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7488_neg : (247180129 / 1000000000) ≤ -Real.log (781 / 1000) ∧
    -Real.log (781 / 1000) ≤ (24718013 / 100000000) := by
  have h := checkLog_sound (w := (219 / 1781)) (n := 12)
    (lo := (247180129 / 1000000000)) (hi := (24718013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 781) = 1/(781 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7488 : Bounds (-24718013 / 100000000) (-247180129 / 1000000000) (Real.log (781 / 1000)) := by
  have h := reflection_log_7488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7489_neg : (6843 / 31250000) ≤ -Real.log (1000000 / 1000219) ∧
    -Real.log (1000000 / 1000219) ≤ (218977 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 2000219)) (n := 12)
    (lo := (6843 / 31250000)) (hi := (218977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000219 / 1000000) = 1/(1000000 / 1000219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7489 : Bounds (6843 / 31250000) (218977 / 1000000000) (Real.log (1000219 / 1000000)) := by
  have h := reflection_log_7489_neg
  have he : Real.log (1000219 / 1000000) = -Real.log (1000000 / 1000219) := by
    rw [show ((1000219 / 1000000) : ℝ) = ((1000000 / 1000219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7490_neg : (219023 / 1000000000) ≤ -Real.log (999781 / 1000000) ∧
    -Real.log (999781 / 1000000) ≤ (13689 / 62500000) := by
  have h := checkLog_sound (w := (219 / 1999781)) (n := 12)
    (lo := (219023 / 1000000000)) (hi := (13689 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999781) = 1/(999781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7490 : Bounds (-13689 / 62500000) (-219023 / 1000000000) (Real.log (999781 / 1000000)) := by
  have h := reflection_log_7490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7491_neg : (104445597 / 1000000000) ≤ -Real.log (200000 / 222019) ∧
    -Real.log (200000 / 222019) ≤ (52222799 / 500000000) := by
  have h := checkLog_sound (w := (22019 / 422019)) (n := 12)
    (lo := (104445597 / 1000000000)) (hi := (52222799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222019 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222019 / 200000) = 1/(200000 / 222019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7491 : Bounds (104445597 / 1000000000) (52222799 / 500000000) (Real.log (222019 / 200000)) := by
  have h := reflection_log_7491_neg
  have he : Real.log (222019 / 200000) = -Real.log (200000 / 222019) := by
    rw [show ((222019 / 200000) : ℝ) = ((200000 / 222019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7492_neg : (116640563 / 1000000000) ≤ -Real.log (177981 / 200000) ∧
    -Real.log (177981 / 200000) ≤ (29160141 / 250000000) := by
  have h := checkLog_sound (w := (22019 / 377981)) (n := 12)
    (lo := (116640563 / 1000000000)) (hi := (29160141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 177981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 177981) = 1/(177981 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7492 : Bounds (-29160141 / 250000000) (-116640563 / 1000000000) (Real.log (177981 / 200000)) := by
  have h := reflection_log_7492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7493_neg : (104873397 / 1000000000) ≤ -Real.log (100000 / 111057) ∧
    -Real.log (100000 / 111057) ≤ (52436699 / 500000000) := by
  have h := checkLog_sound (w := (11057 / 211057)) (n := 12)
    (lo := (104873397 / 1000000000)) (hi := (52436699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111057 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111057 / 100000) = 1/(100000 / 111057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7493 : Bounds (104873397 / 1000000000) (52436699 / 500000000) (Real.log (111057 / 100000)) := by
  have h := reflection_log_7493_neg
  have he : Real.log (111057 / 100000) = -Real.log (100000 / 111057) := by
    rw [show ((111057 / 100000) : ℝ) = ((100000 / 111057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7494_neg : (11717447 / 100000000) ≤ -Real.log (88943 / 100000) ∧
    -Real.log (88943 / 100000) ≤ (117174471 / 1000000000) := by
  have h := checkLog_sound (w := (11057 / 188943)) (n := 12)
    (lo := (11717447 / 100000000)) (hi := (117174471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 88943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 88943) = 1/(88943 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7494 : Bounds (-117174471 / 1000000000) (-11717447 / 100000000) (Real.log (88943 / 100000)) := by
  have h := reflection_log_7494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7495_neg : (12301073 / 1000000000) ≤ -Real.log (9877742751 / 10000000000) ∧
    -Real.log (9877742751 / 10000000000) ≤ (6150537 / 500000000) := by
  have h := checkLog_sound (w := (122257249 / 19877742751)) (n := 12)
    (lo := (12301073 / 1000000000)) (hi := (6150537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9877742751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9877742751) = 1/(9877742751 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7495 : Bounds (-6150537 / 500000000) (-12301073 / 1000000000) (Real.log (9877742751 / 10000000000)) := by
  have h := reflection_log_7495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7496_neg : (6097483 / 500000000) ≤ -Real.log (39515163639 / 40000000000) ∧
    -Real.log (39515163639 / 40000000000) ≤ (12194967 / 1000000000) := by
  have h := checkLog_sound (w := (484836361 / 79515163639)) (n := 12)
    (lo := (6097483 / 500000000)) (hi := (12194967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39515163639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39515163639) = 1/(39515163639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7496 : Bounds (-12194967 / 1000000000) (-6097483 / 500000000) (Real.log (39515163639 / 40000000000)) := by
  have h := reflection_log_7496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7497_neg : (2763577 / 12500000) ≤ -Real.log (500000000000 / 623715452773) ∧
    -Real.log (500000000000 / 623715452773) ≤ (221086161 / 1000000000) := by
  have h := checkLog_sound (w := (123715452773 / 1123715452773)) (n := 12)
    (lo := (2763577 / 12500000)) (hi := (221086161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623715452773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623715452773 / 500000000000) = 1/(500000000000 / 623715452773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7497 : Bounds (2763577 / 12500000) (221086161 / 1000000000) (Real.log (623715452773 / 500000000000)) := by
  have h := reflection_log_7497_neg
  have he : Real.log (623715452773 / 500000000000) = -Real.log (500000000000 / 623715452773) := by
    rw [show ((623715452773 / 500000000000) : ℝ) = ((500000000000 / 623715452773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7498_neg : (222047867 / 1000000000) ≤ -Real.log (15625000000 / 19509861653) ∧
    -Real.log (15625000000 / 19509861653) ≤ (55511967 / 250000000) := by
  have h := checkLog_sound (w := (3884861653 / 35134861653)) (n := 12)
    (lo := (222047867 / 1000000000)) (hi := (55511967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19509861653 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19509861653 / 15625000000) = 1/(15625000000 / 19509861653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7498 : Bounds (222047867 / 1000000000) (55511967 / 250000000) (Real.log (19509861653 / 15625000000)) := by
  have h := reflection_log_7498_neg
  have he : Real.log (19509861653 / 15625000000) = -Real.log (15625000000 / 19509861653) := by
    rw [show ((19509861653 / 15625000000) : ℝ) = ((15625000000 / 19509861653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7499_neg : (444160723 / 1000000000) ≤ -Real.log (50000000000 / 77959053103) ∧
    -Real.log (50000000000 / 77959053103) ≤ (111040181 / 250000000) := by
  have h := checkLog_sound (w := (27959053103 / 127959053103)) (n := 12)
    (lo := (444160723 / 1000000000)) (hi := (111040181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77959053103 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77959053103 / 50000000000) = 1/(50000000000 / 77959053103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7499 : Bounds (444160723 / 1000000000) (111040181 / 250000000) (Real.log (77959053103 / 50000000000)) := by
  have h := reflection_log_7499_neg
  have he : Real.log (77959053103 / 50000000000) = -Real.log (50000000000 / 77959053103) := by
    rw [show ((77959053103 / 50000000000) : ℝ) = ((50000000000 / 77959053103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7500_neg : (445210979 / 1000000000) ≤ -Real.log (250000000000 / 390204865557) ∧
    -Real.log (250000000000 / 390204865557) ≤ (22260549 / 50000000) := by
  have h := checkLog_sound (w := (140204865557 / 640204865557)) (n := 12)
    (lo := (445210979 / 1000000000)) (hi := (22260549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390204865557 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390204865557 / 250000000000) = 1/(250000000000 / 390204865557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7500 : Bounds (445210979 / 1000000000) (22260549 / 50000000) (Real.log (390204865557 / 250000000000)) := by
  have h := reflection_log_7500_neg
  have he : Real.log (390204865557 / 250000000000) = -Real.log (250000000000 / 390204865557) := by
    rw [show ((390204865557 / 250000000000) : ℝ) = ((250000000000 / 390204865557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7501_neg : (99220469 / 500000000) ≤ -Real.log (2000 / 2439) ∧
    -Real.log (2000 / 2439) ≤ (198440939 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 4439)) (n := 12)
    (lo := (99220469 / 500000000)) (hi := (198440939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2439 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2439 / 2000) = 1/(2000 / 2439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7501 : Bounds (99220469 / 500000000) (198440939 / 1000000000) (Real.log (2439 / 2000)) := by
  have h := reflection_log_7501_neg
  have he : Real.log (2439 / 2000) = -Real.log (2000 / 2439) := by
    rw [show ((2439 / 2000) : ℝ) = ((2000 / 2439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7502_neg : (247820539 / 1000000000) ≤ -Real.log (1561 / 2000) ∧
    -Real.log (1561 / 2000) ≤ (12391027 / 50000000) := by
  have h := checkLog_sound (w := (439 / 3561)) (n := 12)
    (lo := (247820539 / 1000000000)) (hi := (12391027 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1561) = 1/(1561 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7502 : Bounds (-12391027 / 50000000) (-247820539 / 1000000000) (Real.log (1561 / 2000)) := by
  have h := reflection_log_7502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7503_neg : (8779 / 40000000) ≤ -Real.log (2000000 / 2000439) ∧
    -Real.log (2000000 / 2000439) ≤ (54869 / 250000000) := by
  have h := checkLog_sound (w := (439 / 4000439)) (n := 12)
    (lo := (8779 / 40000000)) (hi := (54869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000439 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000439 / 2000000) = 1/(2000000 / 2000439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7503 : Bounds (8779 / 40000000) (54869 / 250000000) (Real.log (2000439 / 2000000)) := by
  have h := reflection_log_7503_neg
  have he : Real.log (2000439 / 2000000) = -Real.log (2000000 / 2000439) := by
    rw [show ((2000439 / 2000000) : ℝ) = ((2000000 / 2000439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7504_neg : (54881 / 250000000) ≤ -Real.log (1999561 / 2000000) ∧
    -Real.log (1999561 / 2000000) ≤ (8781 / 40000000) := by
  have h := checkLog_sound (w := (439 / 3999561)) (n := 12)
    (lo := (54881 / 250000000)) (hi := (8781 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999561) = 1/(1999561 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7504 : Bounds (-8781 / 40000000) (-54881 / 250000000) (Real.log (1999561 / 2000000)) := by
  have h := reflection_log_7504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7505_neg : (52338541 / 500000000) ≤ -Real.log (62500 / 69397) ∧
    -Real.log (62500 / 69397) ≤ (104677083 / 1000000000) := by
  have h := checkLog_sound (w := (6897 / 131897)) (n := 12)
    (lo := (52338541 / 500000000)) (hi := (104677083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69397 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69397 / 62500) = 1/(62500 / 69397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7505 : Bounds (52338541 / 500000000) (104677083 / 1000000000) (Real.log (69397 / 62500)) := by
  have h := reflection_log_7505_neg
  have he : Real.log (69397 / 62500) = -Real.log (62500 / 69397) := by
    rw [show ((69397 / 62500) : ℝ) = ((62500 / 69397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7506_neg : (584647 / 5000000) ≤ -Real.log (55603 / 62500) ∧
    -Real.log (55603 / 62500) ≤ (116929401 / 1000000000) := by
  have h := checkLog_sound (w := (6897 / 118103)) (n := 12)
    (lo := (584647 / 5000000)) (hi := (116929401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55603) = 1/(55603 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7506 : Bounds (-116929401 / 1000000000) (-584647 / 5000000) (Real.log (55603 / 62500)) := by
  have h := reflection_log_7506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7507_neg : (52552391 / 500000000) ≤ -Real.log (1000000 / 1110827) ∧
    -Real.log (1000000 / 1110827) ≤ (105104783 / 1000000000) := by
  have h := checkLog_sound (w := (110827 / 2110827)) (n := 12)
    (lo := (52552391 / 500000000)) (hi := (105104783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1110827 / 1000000) = 1/(1000000 / 1110827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7507 : Bounds (52552391 / 500000000) (105104783 / 1000000000) (Real.log (1110827 / 1000000)) := by
  have h := reflection_log_7507_neg
  have he : Real.log (1110827 / 1000000) = -Real.log (1000000 / 1110827) := by
    rw [show ((1110827 / 1000000) : ℝ) = ((1000000 / 1110827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7508_neg : (117463461 / 1000000000) ≤ -Real.log (889173 / 1000000) ∧
    -Real.log (889173 / 1000000) ≤ (58731731 / 500000000) := by
  have h := checkLog_sound (w := (110827 / 1889173)) (n := 12)
    (lo := (117463461 / 1000000000)) (hi := (58731731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 889173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 889173) = 1/(889173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7508 : Bounds (-58731731 / 500000000) (-117463461 / 1000000000) (Real.log (889173 / 1000000)) := by
  have h := reflection_log_7508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7509_neg : (6179339 / 500000000) ≤ -Real.log (987717376071 / 1000000000000) ∧
    -Real.log (987717376071 / 1000000000000) ≤ (12358679 / 1000000000) := by
  have h := checkLog_sound (w := (12282623929 / 1987717376071)) (n := 12)
    (lo := (6179339 / 500000000)) (hi := (12358679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987717376071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987717376071) = 1/(987717376071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7509 : Bounds (-12358679 / 1000000000) (-6179339 / 500000000) (Real.log (987717376071 / 1000000000000)) := by
  have h := reflection_log_7509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7510_neg : (12252317 / 1000000000) ≤ -Real.log (3858681391 / 3906250000) ∧
    -Real.log (3858681391 / 3906250000) ≤ (6126159 / 500000000) := by
  have h := checkLog_sound (w := (47568609 / 7764931391)) (n := 12)
    (lo := (12252317 / 1000000000)) (hi := (6126159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3858681391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3858681391) = 1/(3858681391 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7510 : Bounds (-6126159 / 500000000) (-12252317 / 1000000000) (Real.log (3858681391 / 3906250000)) := by
  have h := reflection_log_7510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7511_neg : (110803241 / 500000000) ≤ -Real.log (25000000000 / 31202003489) ∧
    -Real.log (25000000000 / 31202003489) ≤ (221606483 / 1000000000) := by
  have h := checkLog_sound (w := (6202003489 / 56202003489)) (n := 12)
    (lo := (110803241 / 500000000)) (hi := (221606483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31202003489 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31202003489 / 25000000000) = 1/(25000000000 / 31202003489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7511 : Bounds (110803241 / 500000000) (221606483 / 1000000000) (Real.log (31202003489 / 25000000000)) := by
  have h := reflection_log_7511_neg
  have he : Real.log (31202003489 / 25000000000) = -Real.log (25000000000 / 31202003489) := by
    rw [show ((31202003489 / 25000000000) : ℝ) = ((25000000000 / 31202003489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7512_neg : (55642061 / 250000000) ≤ -Real.log (500000000000 / 624640536769) ∧
    -Real.log (500000000000 / 624640536769) ≤ (44513649 / 200000000) := by
  have h := checkLog_sound (w := (124640536769 / 1124640536769)) (n := 12)
    (lo := (55642061 / 250000000)) (hi := (44513649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624640536769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624640536769 / 500000000000) = 1/(500000000000 / 624640536769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7512 : Bounds (55642061 / 250000000) (44513649 / 200000000) (Real.log (624640536769 / 500000000000)) := by
  have h := reflection_log_7512_neg
  have he : Real.log (624640536769 / 500000000000) = -Real.log (500000000000 / 624640536769) := by
    rw [show ((624640536769 / 500000000000) : ℝ) = ((500000000000 / 624640536769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7513_neg : (445210979 / 1000000000) ≤ -Real.log (500000000000 / 780409731113) ∧
    -Real.log (500000000000 / 780409731113) ≤ (22260549 / 50000000) := by
  have h := checkLog_sound (w := (280409731113 / 1280409731113)) (n := 12)
    (lo := (445210979 / 1000000000)) (hi := (22260549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780409731113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780409731113 / 500000000000) = 1/(500000000000 / 780409731113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7513 : Bounds (445210979 / 1000000000) (22260549 / 50000000) (Real.log (780409731113 / 500000000000)) := by
  have h := reflection_log_7513_neg
  have he : Real.log (780409731113 / 500000000000) = -Real.log (500000000000 / 780409731113) := by
    rw [show ((780409731113 / 500000000000) : ℝ) = ((500000000000 / 780409731113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7514_neg : (446261477 / 1000000000) ≤ -Real.log (250000000000 / 390614990391) ∧
    -Real.log (250000000000 / 390614990391) ≤ (223130739 / 500000000) := by
  have h := checkLog_sound (w := (140614990391 / 640614990391)) (n := 12)
    (lo := (446261477 / 1000000000)) (hi := (223130739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390614990391 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390614990391 / 250000000000) = 1/(250000000000 / 390614990391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7514 : Bounds (446261477 / 1000000000) (223130739 / 500000000) (Real.log (390614990391 / 250000000000)) := by
  have h := reflection_log_7514_neg
  have he : Real.log (390614990391 / 250000000000) = -Real.log (250000000000 / 390614990391) := by
    rw [show ((390614990391 / 250000000000) : ℝ) = ((250000000000 / 390614990391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7515_neg : (99425429 / 500000000) ≤ -Real.log (50 / 61) ∧
    -Real.log (50 / 61) ≤ (198850859 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 111)) (n := 12)
    (lo := (99425429 / 500000000)) (hi := (198850859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 50) = 1/(50 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7515 : Bounds (99425429 / 500000000) (198850859 / 1000000000) (Real.log (61 / 50)) := by
  have h := reflection_log_7515_neg
  have he : Real.log (61 / 50) = -Real.log (50 / 61) := by
    rw [show ((61 / 50) : ℝ) = ((50 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7516_neg : (248461359 / 1000000000) ≤ -Real.log (39 / 50) ∧
    -Real.log (39 / 50) ≤ (3105767 / 12500000) := by
  have h := checkLog_sound (w := (11 / 89)) (n := 12)
    (lo := (248461359 / 1000000000)) (hi := (3105767 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 39) = 1/(39 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7516 : Bounds (-3105767 / 12500000) (-248461359 / 1000000000) (Real.log (39 / 50)) := by
  have h := reflection_log_7516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7517_neg : (8799 / 40000000) ≤ -Real.log (50000 / 50011) ∧
    -Real.log (50000 / 50011) ≤ (27497 / 125000000) := by
  have h := checkLog_sound (w := (11 / 100011)) (n := 12)
    (lo := (8799 / 40000000)) (hi := (27497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50011 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50011 / 50000) = 1/(50000 / 50011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7517 : Bounds (8799 / 40000000) (27497 / 125000000) (Real.log (50011 / 50000)) := by
  have h := reflection_log_7517_neg
  have he : Real.log (50011 / 50000) = -Real.log (50000 / 50011) := by
    rw [show ((50011 / 50000) : ℝ) = ((50000 / 50011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7518_neg : (27503 / 125000000) ≤ -Real.log (49989 / 50000) ∧
    -Real.log (49989 / 50000) ≤ (8801 / 40000000) := by
  have h := checkLog_sound (w := (11 / 99989)) (n := 12)
    (lo := (27503 / 125000000)) (hi := (8801 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49989) = 1/(49989 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7518 : Bounds (-8801 / 40000000) (-27503 / 125000000) (Real.log (49989 / 50000)) := by
  have h := reflection_log_7518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7519_neg : (104907613 / 1000000000) ≤ -Real.log (62500 / 69413) ∧
    -Real.log (62500 / 69413) ≤ (52453807 / 500000000) := by
  have h := checkLog_sound (w := (6913 / 131913)) (n := 12)
    (lo := (104907613 / 1000000000)) (hi := (52453807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69413 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69413 / 62500) = 1/(62500 / 69413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7519 : Bounds (104907613 / 1000000000) (52453807 / 500000000) (Real.log (69413 / 62500)) := by
  have h := reflection_log_7519_neg
  have he : Real.log (69413 / 62500) = -Real.log (62500 / 69413) := by
    rw [show ((69413 / 62500) : ℝ) = ((62500 / 69413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7520_neg : (23443439 / 200000000) ≤ -Real.log (55587 / 62500) ∧
    -Real.log (55587 / 62500) ≤ (29304299 / 250000000) := by
  have h := checkLog_sound (w := (6913 / 118087)) (n := 12)
    (lo := (23443439 / 200000000)) (hi := (29304299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55587) = 1/(55587 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7520 : Bounds (-29304299 / 250000000) (-23443439 / 200000000) (Real.log (55587 / 62500)) := by
  have h := reflection_log_7520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7521_neg : (21067223 / 200000000) ≤ -Real.log (250000 / 277771) ∧
    -Real.log (250000 / 277771) ≤ (26334029 / 250000000) := by
  have h := checkLog_sound (w := (27771 / 527771)) (n := 12)
    (lo := (21067223 / 200000000)) (hi := (26334029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277771 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(277771 / 250000) = 1/(250000 / 277771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7521 : Bounds (21067223 / 200000000) (26334029 / 250000000) (Real.log (277771 / 250000)) := by
  have h := reflection_log_7521_neg
  have he : Real.log (277771 / 250000) = -Real.log (250000 / 277771) := by
    rw [show ((277771 / 250000) : ℝ) = ((250000 / 277771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7522_neg : (14719067 / 125000000) ≤ -Real.log (222229 / 250000) ∧
    -Real.log (222229 / 250000) ≤ (117752537 / 1000000000) := by
  have h := checkLog_sound (w := (27771 / 472229)) (n := 12)
    (lo := (14719067 / 125000000)) (hi := (117752537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 222229) = 1/(222229 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7522 : Bounds (-117752537 / 1000000000) (-14719067 / 125000000) (Real.log (222229 / 250000)) := by
  have h := reflection_log_7522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7523_neg : (620821 / 50000000) ≤ -Real.log (61728771559 / 62500000000) ∧
    -Real.log (61728771559 / 62500000000) ≤ (12416421 / 1000000000) := by
  have h := checkLog_sound (w := (771228441 / 124228771559)) (n := 12)
    (lo := (620821 / 50000000)) (hi := (12416421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61728771559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61728771559) = 1/(61728771559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7523 : Bounds (-12416421 / 1000000000) (-620821 / 50000000) (Real.log (61728771559 / 62500000000)) := by
  have h := reflection_log_7523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7524_neg : (6154791 / 500000000) ≤ -Real.log (3858460431 / 3906250000) ∧
    -Real.log (3858460431 / 3906250000) ≤ (12309583 / 1000000000) := by
  have h := checkLog_sound (w := (47789569 / 7764710431)) (n := 12)
    (lo := (6154791 / 500000000)) (hi := (12309583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3858460431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3858460431) = 1/(3858460431 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7524 : Bounds (-12309583 / 1000000000) (-6154791 / 500000000) (Real.log (3858460431 / 3906250000)) := by
  have h := reflection_log_7524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7525_neg : (27765601 / 125000000) ≤ -Real.log (125000000000 / 156090902549) ∧
    -Real.log (125000000000 / 156090902549) ≤ (222124809 / 1000000000) := by
  have h := checkLog_sound (w := (31090902549 / 281090902549)) (n := 12)
    (lo := (27765601 / 125000000)) (hi := (222124809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156090902549 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156090902549 / 125000000000) = 1/(125000000000 / 156090902549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7525 : Bounds (27765601 / 125000000) (222124809 / 1000000000) (Real.log (156090902549 / 125000000000)) := by
  have h := reflection_log_7525_neg
  have he : Real.log (156090902549 / 125000000000) = -Real.log (125000000000 / 156090902549) := by
    rw [show ((156090902549 / 125000000000) : ℝ) = ((125000000000 / 156090902549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7526_neg : (223088651 / 1000000000) ≤ -Real.log (500000000000 / 624965688547) ∧
    -Real.log (500000000000 / 624965688547) ≤ (55772163 / 250000000) := by
  have h := checkLog_sound (w := (124965688547 / 1124965688547)) (n := 12)
    (lo := (223088651 / 1000000000)) (hi := (55772163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624965688547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624965688547 / 500000000000) = 1/(500000000000 / 624965688547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7526 : Bounds (223088651 / 1000000000) (55772163 / 250000000) (Real.log (624965688547 / 500000000000)) := by
  have h := reflection_log_7526_neg
  have he : Real.log (624965688547 / 500000000000) = -Real.log (500000000000 / 624965688547) := by
    rw [show ((624965688547 / 500000000000) : ℝ) = ((500000000000 / 624965688547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7527_neg : (446261477 / 1000000000) ≤ -Real.log (500000000000 / 781229980781) ∧
    -Real.log (500000000000 / 781229980781) ≤ (223130739 / 500000000) := by
  have h := checkLog_sound (w := (281229980781 / 1281229980781)) (n := 12)
    (lo := (446261477 / 1000000000)) (hi := (223130739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781229980781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781229980781 / 500000000000) = 1/(500000000000 / 781229980781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7527 : Bounds (446261477 / 1000000000) (223130739 / 500000000) (Real.log (781229980781 / 500000000000)) := by
  have h := reflection_log_7527_neg
  have he : Real.log (781229980781 / 500000000000) = -Real.log (500000000000 / 781229980781) := by
    rw [show ((781229980781 / 500000000000) : ℝ) = ((500000000000 / 781229980781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7528_neg : (223656109 / 500000000) ≤ -Real.log (125000000000 / 195512820513) ∧
    -Real.log (125000000000 / 195512820513) ≤ (447312219 / 1000000000) := by
  have h := checkLog_sound (w := (70512820513 / 320512820513)) (n := 12)
    (lo := (223656109 / 500000000)) (hi := (447312219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195512820513 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195512820513 / 125000000000) = 1/(125000000000 / 195512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7528 : Bounds (223656109 / 500000000) (447312219 / 1000000000) (Real.log (195512820513 / 125000000000)) := by
  have h := reflection_log_7528_neg
  have he : Real.log (195512820513 / 125000000000) = -Real.log (125000000000 / 195512820513) := by
    rw [show ((195512820513 / 125000000000) : ℝ) = ((125000000000 / 195512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7529_neg : (19926061 / 100000000) ≤ -Real.log (2000 / 2441) ∧
    -Real.log (2000 / 2441) ≤ (199260611 / 1000000000) := by
  have h := checkLog_sound (w := (441 / 4441)) (n := 12)
    (lo := (19926061 / 100000000)) (hi := (199260611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2441 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2441 / 2000) = 1/(2000 / 2441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7529 : Bounds (19926061 / 100000000) (199260611 / 1000000000) (Real.log (2441 / 2000)) := by
  have h := reflection_log_7529_neg
  have he : Real.log (2441 / 2000) = -Real.log (2000 / 2441) := by
    rw [show ((2441 / 2000) : ℝ) = ((2000 / 2441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7530_neg : (24910259 / 100000000) ≤ -Real.log (1559 / 2000) ∧
    -Real.log (1559 / 2000) ≤ (249102591 / 1000000000) := by
  have h := checkLog_sound (w := (441 / 3559)) (n := 12)
    (lo := (24910259 / 100000000)) (hi := (249102591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1559) = 1/(1559 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7530 : Bounds (-249102591 / 1000000000) (-24910259 / 100000000) (Real.log (1559 / 2000)) := by
  have h := reflection_log_7530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7531_neg : (8819 / 40000000) ≤ -Real.log (2000000 / 2000441) ∧
    -Real.log (2000000 / 2000441) ≤ (55119 / 250000000) := by
  have h := checkLog_sound (w := (441 / 4000441)) (n := 12)
    (lo := (8819 / 40000000)) (hi := (55119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000441 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000441 / 2000000) = 1/(2000000 / 2000441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7531 : Bounds (8819 / 40000000) (55119 / 250000000) (Real.log (2000441 / 2000000)) := by
  have h := reflection_log_7531_neg
  have he : Real.log (2000441 / 2000000) = -Real.log (2000000 / 2000441) := by
    rw [show ((2000441 / 2000000) : ℝ) = ((2000000 / 2000441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7532_neg : (55131 / 250000000) ≤ -Real.log (1999559 / 2000000) ∧
    -Real.log (1999559 / 2000000) ≤ (8821 / 40000000) := by
  have h := checkLog_sound (w := (441 / 3999559)) (n := 12)
    (lo := (55131 / 250000000)) (hi := (8821 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999559) = 1/(1999559 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7532 : Bounds (-8821 / 40000000) (-55131 / 250000000) (Real.log (1999559 / 2000000)) := by
  have h := reflection_log_7532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7533_neg : (10513809 / 100000000) ≤ -Real.log (62500 / 69429) ∧
    -Real.log (62500 / 69429) ≤ (105138091 / 1000000000) := by
  have h := checkLog_sound (w := (6929 / 131929)) (n := 12)
    (lo := (10513809 / 100000000)) (hi := (105138091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69429 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69429 / 62500) = 1/(62500 / 69429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7533 : Bounds (10513809 / 100000000) (105138091 / 1000000000) (Real.log (69429 / 62500)) := by
  have h := reflection_log_7533_neg
  have he : Real.log (69429 / 62500) = -Real.log (62500 / 69429) := by
    rw [show ((69429 / 62500) : ℝ) = ((62500 / 69429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7534_neg : (58752537 / 500000000) ≤ -Real.log (55571 / 62500) ∧
    -Real.log (55571 / 62500) ≤ (4700203 / 40000000) := by
  have h := checkLog_sound (w := (6929 / 118071)) (n := 12)
    (lo := (58752537 / 500000000)) (hi := (4700203 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55571) = 1/(55571 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7534 : Bounds (-4700203 / 40000000) (-58752537 / 500000000) (Real.log (55571 / 62500)) := by
  have h := reflection_log_7534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7535_neg : (52783247 / 500000000) ≤ -Real.log (50000 / 55567) ∧
    -Real.log (50000 / 55567) ≤ (21113299 / 200000000) := by
  have h := checkLog_sound (w := (5567 / 105567)) (n := 12)
    (lo := (52783247 / 500000000)) (hi := (21113299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55567 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55567 / 50000) = 1/(50000 / 55567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7535 : Bounds (52783247 / 500000000) (21113299 / 200000000) (Real.log (55567 / 50000)) := by
  have h := reflection_log_7535_neg
  have he : Real.log (55567 / 50000) = -Real.log (50000 / 55567) := by
    rw [show ((55567 / 50000) : ℝ) = ((50000 / 55567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7536_neg : (14755071 / 125000000) ≤ -Real.log (44433 / 50000) ∧
    -Real.log (44433 / 50000) ≤ (118040569 / 1000000000) := by
  have h := checkLog_sound (w := (5567 / 94433)) (n := 12)
    (lo := (14755071 / 125000000)) (hi := (118040569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44433) = 1/(44433 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7536 : Bounds (-118040569 / 1000000000) (-14755071 / 125000000) (Real.log (44433 / 50000)) := by
  have h := reflection_log_7536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7537_neg : (6237037 / 500000000) ≤ -Real.log (2469008511 / 2500000000) ∧
    -Real.log (2469008511 / 2500000000) ≤ (498963 / 40000000) := by
  have h := checkLog_sound (w := (30991489 / 4969008511)) (n := 12)
    (lo := (6237037 / 500000000)) (hi := (498963 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2469008511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2469008511) = 1/(2469008511 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7537 : Bounds (-498963 / 40000000) (-6237037 / 500000000) (Real.log (2469008511 / 2500000000)) := by
  have h := reflection_log_7537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7538_neg : (12366983 / 1000000000) ≤ -Real.log (3858238959 / 3906250000) ∧
    -Real.log (3858238959 / 3906250000) ≤ (1545873 / 125000000) := by
  have h := checkLog_sound (w := (48011041 / 7764488959)) (n := 12)
    (lo := (12366983 / 1000000000)) (hi := (1545873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3858238959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3858238959) = 1/(3858238959 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7538 : Bounds (-1545873 / 125000000) (-12366983 / 1000000000) (Real.log (3858238959 / 3906250000)) := by
  have h := reflection_log_7538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7539_neg : (44528633 / 200000000) ≤ -Real.log (12500000000 / 15617183423) ∧
    -Real.log (12500000000 / 15617183423) ≤ (111321583 / 500000000) := by
  have h := checkLog_sound (w := (3117183423 / 28117183423)) (n := 12)
    (lo := (44528633 / 200000000)) (hi := (111321583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15617183423 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15617183423 / 12500000000) = 1/(12500000000 / 15617183423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7539 : Bounds (44528633 / 200000000) (111321583 / 500000000) (Real.log (15617183423 / 12500000000)) := by
  have h := reflection_log_7539_neg
  have he : Real.log (15617183423 / 12500000000) = -Real.log (12500000000 / 15617183423) := by
    rw [show ((15617183423 / 12500000000) : ℝ) = ((12500000000 / 15617183423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7540_neg : (223607063 / 1000000000) ≤ -Real.log (250000000000 / 312644881057) ∧
    -Real.log (250000000000 / 312644881057) ≤ (27950883 / 125000000) := by
  have h := checkLog_sound (w := (62644881057 / 562644881057)) (n := 12)
    (lo := (223607063 / 1000000000)) (hi := (27950883 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312644881057 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312644881057 / 250000000000) = 1/(250000000000 / 312644881057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7540 : Bounds (223607063 / 1000000000) (27950883 / 125000000) (Real.log (312644881057 / 250000000000)) := by
  have h := reflection_log_7540_neg
  have he : Real.log (312644881057 / 250000000000) = -Real.log (250000000000 / 312644881057) := by
    rw [show ((312644881057 / 250000000000) : ℝ) = ((250000000000 / 312644881057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7541_neg : (223656109 / 500000000) ≤ -Real.log (500000000000 / 782051282051) ∧
    -Real.log (500000000000 / 782051282051) ≤ (447312219 / 1000000000) := by
  have h := checkLog_sound (w := (282051282051 / 1282051282051)) (n := 12)
    (lo := (223656109 / 500000000)) (hi := (447312219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782051282051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782051282051 / 500000000000) = 1/(500000000000 / 782051282051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7541 : Bounds (223656109 / 500000000) (447312219 / 1000000000) (Real.log (782051282051 / 500000000000)) := by
  have h := reflection_log_7541_neg
  have he : Real.log (782051282051 / 500000000000) = -Real.log (500000000000 / 782051282051) := by
    rw [show ((782051282051 / 500000000000) : ℝ) = ((500000000000 / 782051282051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7542_neg : (448363201 / 1000000000) ≤ -Real.log (500000000000 / 782873636947) ∧
    -Real.log (500000000000 / 782873636947) ≤ (224181601 / 500000000) := by
  have h := checkLog_sound (w := (282873636947 / 1282873636947)) (n := 12)
    (lo := (448363201 / 1000000000)) (hi := (224181601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782873636947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782873636947 / 500000000000) = 1/(500000000000 / 782873636947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7542 : Bounds (448363201 / 1000000000) (224181601 / 500000000) (Real.log (782873636947 / 500000000000)) := by
  have h := reflection_log_7542_neg
  have he : Real.log (782873636947 / 500000000000) = -Real.log (500000000000 / 782873636947) := by
    rw [show ((782873636947 / 500000000000) : ℝ) = ((500000000000 / 782873636947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7543_neg : (39934039 / 200000000) ≤ -Real.log (1000 / 1221) ∧
    -Real.log (1000 / 1221) ≤ (49917549 / 250000000) := by
  have h := checkLog_sound (w := (221 / 2221)) (n := 12)
    (lo := (39934039 / 200000000)) (hi := (49917549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221 / 1000) = 1/(1000 / 1221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7543 : Bounds (39934039 / 200000000) (49917549 / 250000000) (Real.log (1221 / 1000)) := by
  have h := reflection_log_7543_neg
  have he : Real.log (1221 / 1000) = -Real.log (1000 / 1221) := by
    rw [show ((1221 / 1000) : ℝ) = ((1000 / 1221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7544_neg : (249744233 / 1000000000) ≤ -Real.log (779 / 1000) ∧
    -Real.log (779 / 1000) ≤ (124872117 / 500000000) := by
  have h := checkLog_sound (w := (221 / 1779)) (n := 12)
    (lo := (249744233 / 1000000000)) (hi := (124872117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 779) = 1/(779 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7544 : Bounds (-124872117 / 500000000) (-249744233 / 1000000000) (Real.log (779 / 1000)) := by
  have h := reflection_log_7544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7545_neg : (8839 / 40000000) ≤ -Real.log (1000000 / 1000221) ∧
    -Real.log (1000000 / 1000221) ≤ (13811 / 62500000) := by
  have h := checkLog_sound (w := (221 / 2000221)) (n := 12)
    (lo := (8839 / 40000000)) (hi := (13811 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000221 / 1000000) = 1/(1000000 / 1000221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7545 : Bounds (8839 / 40000000) (13811 / 62500000) (Real.log (1000221 / 1000000)) := by
  have h := reflection_log_7545_neg
  have he : Real.log (1000221 / 1000000) = -Real.log (1000000 / 1000221) := by
    rw [show ((1000221 / 1000000) : ℝ) = ((1000000 / 1000221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7546_neg : (6907 / 31250000) ≤ -Real.log (999779 / 1000000) ∧
    -Real.log (999779 / 1000000) ≤ (8841 / 40000000) := by
  have h := checkLog_sound (w := (221 / 1999779)) (n := 12)
    (lo := (6907 / 31250000)) (hi := (8841 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999779) = 1/(999779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7546 : Bounds (-8841 / 40000000) (-6907 / 31250000) (Real.log (999779 / 1000000)) := by
  have h := reflection_log_7546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7547_neg : (21073883 / 200000000) ≤ -Real.log (1000000 / 1111121) ∧
    -Real.log (1000000 / 1111121) ≤ (13171177 / 125000000) := by
  have h := checkLog_sound (w := (111121 / 2111121)) (n := 12)
    (lo := (21073883 / 200000000)) (hi := (13171177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111121 / 1000000) = 1/(1000000 / 1111121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7547 : Bounds (21073883 / 200000000) (13171177 / 125000000) (Real.log (1111121 / 1000000)) := by
  have h := reflection_log_7547_neg
  have he : Real.log (1111121 / 1000000) = -Real.log (1000000 / 1111121) := by
    rw [show ((1111121 / 1000000) : ℝ) = ((1000000 / 1111121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7548_neg : (1472427 / 12500000) ≤ -Real.log (888879 / 1000000) ∧
    -Real.log (888879 / 1000000) ≤ (117794161 / 1000000000) := by
  have h := checkLog_sound (w := (111121 / 1888879)) (n := 12)
    (lo := (1472427 / 12500000)) (hi := (117794161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888879) = 1/(888879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7548 : Bounds (-117794161 / 1000000000) (-1472427 / 12500000) (Real.log (888879 / 1000000)) := by
  have h := reflection_log_7548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7549_neg : (2644943 / 25000000) ≤ -Real.log (1000000 / 1111597) ∧
    -Real.log (1000000 / 1111597) ≤ (105797721 / 1000000000) := by
  have h := checkLog_sound (w := (111597 / 2111597)) (n := 12)
    (lo := (2644943 / 25000000)) (hi := (105797721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111597 / 1000000) = 1/(1000000 / 1111597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7549 : Bounds (2644943 / 25000000) (105797721 / 1000000000) (Real.log (1111597 / 1000000)) := by
  have h := reflection_log_7549_neg
  have he : Real.log (1111597 / 1000000) = -Real.log (1000000 / 1111597) := by
    rw [show ((1111597 / 1000000) : ℝ) = ((1000000 / 1111597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7550_neg : (11832981 / 100000000) ≤ -Real.log (888403 / 1000000) ∧
    -Real.log (888403 / 1000000) ≤ (118329811 / 1000000000) := by
  have h := checkLog_sound (w := (111597 / 1888403)) (n := 12)
    (lo := (11832981 / 100000000)) (hi := (118329811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888403) = 1/(888403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7550 : Bounds (-118329811 / 1000000000) (-11832981 / 100000000) (Real.log (888403 / 1000000)) := by
  have h := reflection_log_7550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7551_neg : (1253209 / 100000000) ≤ -Real.log (987546109591 / 1000000000000) ∧
    -Real.log (987546109591 / 1000000000000) ≤ (12532091 / 1000000000) := by
  have h := checkLog_sound (w := (12453890409 / 1987546109591)) (n := 12)
    (lo := (1253209 / 100000000)) (hi := (12532091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987546109591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987546109591) = 1/(987546109591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7551 : Bounds (-12532091 / 1000000000) (-1253209 / 100000000) (Real.log (987546109591 / 1000000000000)) := by
  have h := reflection_log_7551_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0118 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7552_neg : (2484949 / 200000000) ≤ -Real.log (987652123359 / 1000000000000) ∧
    -Real.log (987652123359 / 1000000000000) ≤ (6212373 / 500000000) := by
  have h := checkLog_sound (w := (12347876641 / 1987652123359)) (n := 12)
    (lo := (2484949 / 200000000)) (hi := (6212373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987652123359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987652123359) = 1/(987652123359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7552 : Bounds (-6212373 / 500000000) (-2484949 / 200000000) (Real.log (987652123359 / 1000000000000)) := by
  have h := reflection_log_7552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7553_neg : (27895447 / 125000000) ≤ -Real.log (125000000000 / 156253128941) ∧
    -Real.log (125000000000 / 156253128941) ≤ (223163577 / 1000000000) := by
  have h := checkLog_sound (w := (31253128941 / 281253128941)) (n := 12)
    (lo := (27895447 / 125000000)) (hi := (223163577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156253128941 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156253128941 / 125000000000) = 1/(125000000000 / 156253128941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7553 : Bounds (27895447 / 125000000) (223163577 / 1000000000) (Real.log (156253128941 / 125000000000)) := by
  have h := reflection_log_7553_neg
  have he : Real.log (156253128941 / 125000000000) = -Real.log (125000000000 / 156253128941) := by
    rw [show ((156253128941 / 125000000000) : ℝ) = ((125000000000 / 156253128941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7554_neg : (22412753 / 100000000) ≤ -Real.log (250000000000 / 312807644729) ∧
    -Real.log (250000000000 / 312807644729) ≤ (224127531 / 1000000000) := by
  have h := checkLog_sound (w := (62807644729 / 562807644729)) (n := 12)
    (lo := (22412753 / 100000000)) (hi := (224127531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312807644729 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312807644729 / 250000000000) = 1/(250000000000 / 312807644729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7554 : Bounds (22412753 / 100000000) (224127531 / 1000000000) (Real.log (312807644729 / 250000000000)) := by
  have h := reflection_log_7554_neg
  have he : Real.log (312807644729 / 250000000000) = -Real.log (250000000000 / 312807644729) := by
    rw [show ((312807644729 / 250000000000) : ℝ) = ((250000000000 / 312807644729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7555_neg : (448363201 / 1000000000) ≤ -Real.log (250000000000 / 391436818473) ∧
    -Real.log (250000000000 / 391436818473) ≤ (224181601 / 500000000) := by
  have h := checkLog_sound (w := (141436818473 / 641436818473)) (n := 12)
    (lo := (448363201 / 1000000000)) (hi := (224181601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391436818473 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391436818473 / 250000000000) = 1/(250000000000 / 391436818473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7555 : Bounds (448363201 / 1000000000) (224181601 / 500000000) (Real.log (391436818473 / 250000000000)) := by
  have h := reflection_log_7555_neg
  have he : Real.log (391436818473 / 250000000000) = -Real.log (250000000000 / 391436818473) := by
    rw [show ((391436818473 / 250000000000) : ℝ) = ((250000000000 / 391436818473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7556_neg : (112353607 / 250000000) ≤ -Real.log (500000000000 / 783697047497) ∧
    -Real.log (500000000000 / 783697047497) ≤ (449414429 / 1000000000) := by
  have h := checkLog_sound (w := (283697047497 / 1283697047497)) (n := 12)
    (lo := (112353607 / 250000000)) (hi := (449414429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783697047497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783697047497 / 500000000000) = 1/(500000000000 / 783697047497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7556 : Bounds (112353607 / 250000000) (449414429 / 1000000000) (Real.log (783697047497 / 500000000000)) := by
  have h := reflection_log_7556_neg
  have he : Real.log (783697047497 / 500000000000) = -Real.log (500000000000 / 783697047497) := by
    rw [show ((783697047497 / 500000000000) : ℝ) = ((500000000000 / 783697047497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7557_neg : (200079611 / 1000000000) ≤ -Real.log (2000 / 2443) ∧
    -Real.log (2000 / 2443) ≤ (50019903 / 250000000) := by
  have h := checkLog_sound (w := (443 / 4443)) (n := 12)
    (lo := (200079611 / 1000000000)) (hi := (50019903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2443 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2443 / 2000) = 1/(2000 / 2443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7557 : Bounds (200079611 / 1000000000) (50019903 / 250000000) (Real.log (2443 / 2000)) := by
  have h := reflection_log_7557_neg
  have he : Real.log (2443 / 2000) = -Real.log (2000 / 2443) := by
    rw [show ((2443 / 2000) : ℝ) = ((2000 / 2443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7558_neg : (250386287 / 1000000000) ≤ -Real.log (1557 / 2000) ∧
    -Real.log (1557 / 2000) ≤ (15649143 / 62500000) := by
  have h := checkLog_sound (w := (443 / 3557)) (n := 12)
    (lo := (250386287 / 1000000000)) (hi := (15649143 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1557) = 1/(1557 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7558 : Bounds (-15649143 / 62500000) (-250386287 / 1000000000) (Real.log (1557 / 2000)) := by
  have h := reflection_log_7558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7559_neg : (8859 / 40000000) ≤ -Real.log (2000000 / 2000443) ∧
    -Real.log (2000000 / 2000443) ≤ (55369 / 250000000) := by
  have h := checkLog_sound (w := (443 / 4000443)) (n := 12)
    (lo := (8859 / 40000000)) (hi := (55369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000443 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000443 / 2000000) = 1/(2000000 / 2000443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7559 : Bounds (8859 / 40000000) (55369 / 250000000) (Real.log (2000443 / 2000000)) := by
  have h := reflection_log_7559_neg
  have he : Real.log (2000443 / 2000000) = -Real.log (2000000 / 2000443) := by
    rw [show ((2000443 / 2000000) : ℝ) = ((2000000 / 2000443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7560_neg : (55381 / 250000000) ≤ -Real.log (1999557 / 2000000) ∧
    -Real.log (1999557 / 2000000) ≤ (8861 / 40000000) := by
  have h := checkLog_sound (w := (443 / 3999557)) (n := 12)
    (lo := (55381 / 250000000)) (hi := (8861 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999557) = 1/(1999557 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7560 : Bounds (-8861 / 40000000) (-55381 / 250000000) (Real.log (1999557 / 2000000)) := by
  have h := reflection_log_7560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7561_neg : (105599787 / 1000000000) ≤ -Real.log (1000000 / 1111377) ∧
    -Real.log (1000000 / 1111377) ≤ (26399947 / 250000000) := by
  have h := checkLog_sound (w := (111377 / 2111377)) (n := 12)
    (lo := (105599787 / 1000000000)) (hi := (26399947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111377 / 1000000) = 1/(1000000 / 1111377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7561 : Bounds (105599787 / 1000000000) (26399947 / 250000000) (Real.log (1111377 / 1000000)) := by
  have h := reflection_log_7561_neg
  have he : Real.log (1111377 / 1000000) = -Real.log (1000000 / 1111377) := by
    rw [show ((1111377 / 1000000) : ℝ) = ((1000000 / 1111377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7562_neg : (23616441 / 200000000) ≤ -Real.log (888623 / 1000000) ∧
    -Real.log (888623 / 1000000) ≤ (59041103 / 500000000) := by
  have h := checkLog_sound (w := (111377 / 1888623)) (n := 12)
    (lo := (23616441 / 200000000)) (hi := (59041103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888623) = 1/(888623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7562 : Bounds (-59041103 / 500000000) (-23616441 / 200000000) (Real.log (888623 / 1000000)) := by
  have h := reflection_log_7562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7563_neg : (26507223 / 250000000) ≤ -Real.log (500000 / 555927) ∧
    -Real.log (500000 / 555927) ≤ (106028893 / 1000000000) := by
  have h := checkLog_sound (w := (55927 / 1055927)) (n := 12)
    (lo := (26507223 / 250000000)) (hi := (106028893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(555927 / 500000) = 1/(500000 / 555927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7563 : Bounds (26507223 / 250000000) (106028893 / 1000000000) (Real.log (555927 / 500000)) := by
  have h := reflection_log_7563_neg
  have he : Real.log (555927 / 500000) = -Real.log (500000 / 555927) := by
    rw [show ((555927 / 500000) : ℝ) = ((500000 / 555927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7564_neg : (23723827 / 200000000) ≤ -Real.log (444073 / 500000) ∧
    -Real.log (444073 / 500000) ≤ (231678 / 1953125) := by
  have h := checkLog_sound (w := (55927 / 944073)) (n := 12)
    (lo := (23723827 / 200000000)) (hi := (231678 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 444073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 444073) = 1/(444073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7564 : Bounds (-231678 / 1953125) (-23723827 / 200000000) (Real.log (444073 / 500000)) := by
  have h := reflection_log_7564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7565_neg : (6295121 / 500000000) ≤ -Real.log (246872170671 / 250000000000) ∧
    -Real.log (246872170671 / 250000000000) ≤ (12590243 / 1000000000) := by
  have h := checkLog_sound (w := (3127829329 / 496872170671)) (n := 12)
    (lo := (6295121 / 500000000)) (hi := (12590243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246872170671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246872170671) = 1/(246872170671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7565 : Bounds (-12590243 / 1000000000) (-6295121 / 500000000) (Real.log (246872170671 / 250000000000)) := by
  have h := reflection_log_7565_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7566_neg : (6241209 / 500000000) ≤ -Real.log (987595163871 / 1000000000000) ∧
    -Real.log (987595163871 / 1000000000000) ≤ (12482419 / 1000000000) := by
  have h := checkLog_sound (w := (12404836129 / 1987595163871)) (n := 12)
    (lo := (6241209 / 500000000)) (hi := (12482419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987595163871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987595163871) = 1/(987595163871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7566 : Bounds (-12482419 / 1000000000) (-6241209 / 500000000) (Real.log (987595163871 / 1000000000000)) := by
  have h := reflection_log_7566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7567_neg : (27960249 / 125000000) ≤ -Real.log (100000000000 / 125067323263) ∧
    -Real.log (100000000000 / 125067323263) ≤ (223681993 / 1000000000) := by
  have h := checkLog_sound (w := (25067323263 / 225067323263)) (n := 12)
    (lo := (27960249 / 125000000)) (hi := (223681993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125067323263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125067323263 / 100000000000) = 1/(100000000000 / 125067323263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7567 : Bounds (27960249 / 125000000) (223681993 / 1000000000) (Real.log (125067323263 / 100000000000)) := by
  have h := reflection_log_7567_neg
  have he : Real.log (125067323263 / 100000000000) = -Real.log (100000000000 / 125067323263) := by
    rw [show ((125067323263 / 100000000000) : ℝ) = ((100000000000 / 125067323263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7568_neg : (224648027 / 1000000000) ≤ -Real.log (125000000000 / 156485251299) ∧
    -Real.log (125000000000 / 156485251299) ≤ (56162007 / 250000000) := by
  have h := checkLog_sound (w := (31485251299 / 281485251299)) (n := 12)
    (lo := (224648027 / 1000000000)) (hi := (56162007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156485251299 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156485251299 / 125000000000) = 1/(125000000000 / 156485251299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7568 : Bounds (224648027 / 1000000000) (56162007 / 250000000) (Real.log (156485251299 / 125000000000)) := by
  have h := reflection_log_7568_neg
  have he : Real.log (156485251299 / 125000000000) = -Real.log (125000000000 / 156485251299) := by
    rw [show ((156485251299 / 125000000000) : ℝ) = ((125000000000 / 156485251299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7569_neg : (112353607 / 250000000) ≤ -Real.log (62500000000 / 97962130937) ∧
    -Real.log (62500000000 / 97962130937) ≤ (449414429 / 1000000000) := by
  have h := checkLog_sound (w := (35462130937 / 160462130937)) (n := 12)
    (lo := (112353607 / 250000000)) (hi := (449414429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97962130937 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97962130937 / 62500000000) = 1/(62500000000 / 97962130937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7569 : Bounds (112353607 / 250000000) (449414429 / 1000000000) (Real.log (97962130937 / 62500000000)) := by
  have h := reflection_log_7569_neg
  have he : Real.log (97962130937 / 62500000000) = -Real.log (62500000000 / 97962130937) := by
    rw [show ((97962130937 / 62500000000) : ℝ) = ((62500000000 / 97962130937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7570_neg : (450465899 / 1000000000) ≤ -Real.log (62500000000 / 98065189467) ∧
    -Real.log (62500000000 / 98065189467) ≤ (4504659 / 10000000) := by
  have h := checkLog_sound (w := (35565189467 / 160565189467)) (n := 12)
    (lo := (450465899 / 1000000000)) (hi := (4504659 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98065189467 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98065189467 / 62500000000) = 1/(62500000000 / 98065189467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7570 : Bounds (450465899 / 1000000000) (4504659 / 10000000) (Real.log (98065189467 / 62500000000)) := by
  have h := reflection_log_7570_neg
  have he : Real.log (98065189467 / 62500000000) = -Real.log (62500000000 / 98065189467) := by
    rw [show ((98065189467 / 62500000000) : ℝ) = ((62500000000 / 98065189467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7571_neg : (10024443 / 50000000) ≤ -Real.log (500 / 611) ∧
    -Real.log (500 / 611) ≤ (200488861 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 1111)) (n := 12)
    (lo := (10024443 / 50000000)) (hi := (200488861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611 / 500) = 1/(500 / 611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7571 : Bounds (10024443 / 50000000) (200488861 / 1000000000) (Real.log (611 / 500)) := by
  have h := reflection_log_7571_neg
  have he : Real.log (611 / 500) = -Real.log (500 / 611) := by
    rw [show ((611 / 500) : ℝ) = ((500 / 611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7572_neg : (125514377 / 500000000) ≤ -Real.log (389 / 500) ∧
    -Real.log (389 / 500) ≤ (50205751 / 200000000) := by
  have h := checkLog_sound (w := (111 / 889)) (n := 12)
    (lo := (125514377 / 500000000)) (hi := (50205751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 389) = 1/(389 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7572 : Bounds (-50205751 / 200000000) (-125514377 / 500000000) (Real.log (389 / 500)) := by
  have h := reflection_log_7572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7573_neg : (8879 / 40000000) ≤ -Real.log (500000 / 500111) ∧
    -Real.log (500000 / 500111) ≤ (27747 / 125000000) := by
  have h := checkLog_sound (w := (111 / 1000111)) (n := 12)
    (lo := (8879 / 40000000)) (hi := (27747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500111 / 500000) = 1/(500000 / 500111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7573 : Bounds (8879 / 40000000) (27747 / 125000000) (Real.log (500111 / 500000)) := by
  have h := reflection_log_7573_neg
  have he : Real.log (500111 / 500000) = -Real.log (500000 / 500111) := by
    rw [show ((500111 / 500000) : ℝ) = ((500000 / 500111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7574_neg : (27753 / 125000000) ≤ -Real.log (499889 / 500000) ∧
    -Real.log (499889 / 500000) ≤ (8881 / 40000000) := by
  have h := checkLog_sound (w := (111 / 999889)) (n := 12)
    (lo := (27753 / 125000000)) (hi := (8881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499889) = 1/(499889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7574 : Bounds (-8881 / 40000000) (-27753 / 125000000) (Real.log (499889 / 500000)) := by
  have h := reflection_log_7574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7575_neg : (26457751 / 250000000) ≤ -Real.log (500000 / 555817) ∧
    -Real.log (500000 / 555817) ≤ (21166201 / 200000000) := by
  have h := checkLog_sound (w := (55817 / 1055817)) (n := 12)
    (lo := (26457751 / 250000000)) (hi := (21166201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(555817 / 500000) = 1/(500000 / 555817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7575 : Bounds (26457751 / 250000000) (21166201 / 200000000) (Real.log (555817 / 500000)) := by
  have h := reflection_log_7575_neg
  have he : Real.log (555817 / 500000) = -Real.log (500000 / 555817) := by
    rw [show ((555817 / 500000) : ℝ) = ((500000 / 555817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7576_neg : (59185729 / 500000000) ≤ -Real.log (444183 / 500000) ∧
    -Real.log (444183 / 500000) ≤ (118371459 / 1000000000) := by
  have h := checkLog_sound (w := (55817 / 944183)) (n := 12)
    (lo := (59185729 / 500000000)) (hi := (118371459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 444183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 444183) = 1/(444183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7576 : Bounds (-118371459 / 1000000000) (-59185729 / 500000000) (Real.log (444183 / 500000)) := by
  have h := reflection_log_7576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7577_neg : (10626091 / 100000000) ≤ -Real.log (62500 / 69507) ∧
    -Real.log (62500 / 69507) ≤ (106260911 / 1000000000) := by
  have h := checkLog_sound (w := (7007 / 132007)) (n := 12)
    (lo := (10626091 / 100000000)) (hi := (106260911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69507 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69507 / 62500) = 1/(62500 / 69507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7577 : Bounds (10626091 / 100000000) (106260911 / 1000000000) (Real.log (69507 / 62500)) := by
  have h := reflection_log_7577_neg
  have he : Real.log (69507 / 62500) = -Real.log (62500 / 69507) := by
    rw [show ((69507 / 62500) : ℝ) = ((62500 / 69507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7578_neg : (11890967 / 100000000) ≤ -Real.log (55493 / 62500) ∧
    -Real.log (55493 / 62500) ≤ (118909671 / 1000000000) := by
  have h := checkLog_sound (w := (7007 / 117993)) (n := 12)
    (lo := (11890967 / 100000000)) (hi := (118909671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55493) = 1/(55493 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7578 : Bounds (-118909671 / 1000000000) (-11890967 / 100000000) (Real.log (55493 / 62500)) := by
  have h := reflection_log_7578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7579_neg : (12648759 / 1000000000) ≤ -Real.log (3857151951 / 3906250000) ∧
    -Real.log (3857151951 / 3906250000) ≤ (316219 / 25000000) := by
  have h := checkLog_sound (w := (49098049 / 7763401951)) (n := 12)
    (lo := (12648759 / 1000000000)) (hi := (316219 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3857151951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3857151951) = 1/(3857151951 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7579 : Bounds (-316219 / 25000000) (-12648759 / 1000000000) (Real.log (3857151951 / 3906250000)) := by
  have h := reflection_log_7579_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7580_neg : (12540453 / 1000000000) ≤ -Real.log (246884462511 / 250000000000) ∧
    -Real.log (246884462511 / 250000000000) ≤ (6270227 / 500000000) := by
  have h := checkLog_sound (w := (3115537489 / 496884462511)) (n := 12)
    (lo := (12540453 / 1000000000)) (hi := (6270227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246884462511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246884462511) = 1/(246884462511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7580 : Bounds (-6270227 / 500000000) (-12540453 / 1000000000) (Real.log (246884462511 / 250000000000)) := by
  have h := reflection_log_7580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7581_neg : (224202463 / 1000000000) ≤ -Real.log (500000000000 / 625662170771) ∧
    -Real.log (500000000000 / 625662170771) ≤ (7006327 / 31250000) := by
  have h := checkLog_sound (w := (125662170771 / 1125662170771)) (n := 12)
    (lo := (224202463 / 1000000000)) (hi := (7006327 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625662170771 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625662170771 / 500000000000) = 1/(500000000000 / 625662170771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7581 : Bounds (224202463 / 1000000000) (7006327 / 31250000) (Real.log (625662170771 / 500000000000)) := by
  have h := reflection_log_7581_neg
  have he : Real.log (625662170771 / 500000000000) = -Real.log (500000000000 / 625662170771) := by
    rw [show ((625662170771 / 500000000000) : ℝ) = ((500000000000 / 625662170771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7582_neg : (11258529 / 50000000) ≤ -Real.log (500000000000 / 626268177969) ∧
    -Real.log (500000000000 / 626268177969) ≤ (225170581 / 1000000000) := by
  have h := checkLog_sound (w := (126268177969 / 1126268177969)) (n := 12)
    (lo := (11258529 / 50000000)) (hi := (225170581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626268177969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626268177969 / 500000000000) = 1/(500000000000 / 626268177969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7582 : Bounds (11258529 / 50000000) (225170581 / 1000000000) (Real.log (626268177969 / 500000000000)) := by
  have h := reflection_log_7582_neg
  have he : Real.log (626268177969 / 500000000000) = -Real.log (500000000000 / 626268177969) := by
    rw [show ((626268177969 / 500000000000) : ℝ) = ((500000000000 / 626268177969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7583_neg : (450465899 / 1000000000) ≤ -Real.log (100000000000 / 156904303147) ∧
    -Real.log (100000000000 / 156904303147) ≤ (4504659 / 10000000) := by
  have h := checkLog_sound (w := (56904303147 / 256904303147)) (n := 12)
    (lo := (450465899 / 1000000000)) (hi := (4504659 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156904303147 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156904303147 / 100000000000) = 1/(100000000000 / 156904303147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7583 : Bounds (450465899 / 1000000000) (4504659 / 10000000) (Real.log (156904303147 / 100000000000)) := by
  have h := reflection_log_7583_neg
  have he : Real.log (156904303147 / 100000000000) = -Real.log (100000000000 / 156904303147) := by
    rw [show ((156904303147 / 100000000000) : ℝ) = ((100000000000 / 156904303147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7584_neg : (90303523 / 200000000) ≤ -Real.log (250000000000 / 392673521851) ∧
    -Real.log (250000000000 / 392673521851) ≤ (28219851 / 62500000) := by
  have h := checkLog_sound (w := (142673521851 / 642673521851)) (n := 12)
    (lo := (90303523 / 200000000)) (hi := (28219851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392673521851 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392673521851 / 250000000000) = 1/(250000000000 / 392673521851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7584 : Bounds (90303523 / 200000000) (28219851 / 62500000) (Real.log (392673521851 / 250000000000)) := by
  have h := reflection_log_7584_neg
  have he : Real.log (392673521851 / 250000000000) = -Real.log (250000000000 / 392673521851) := by
    rw [show ((392673521851 / 250000000000) : ℝ) = ((250000000000 / 392673521851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7585_neg : (100448971 / 500000000) ≤ -Real.log (400 / 489) ∧
    -Real.log (400 / 489) ≤ (200897943 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 889)) (n := 12)
    (lo := (100448971 / 500000000)) (hi := (200897943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489 / 400) = 1/(400 / 489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7585 : Bounds (100448971 / 500000000) (200897943 / 1000000000) (Real.log (489 / 400)) := by
  have h := reflection_log_7585_neg
  have he : Real.log (489 / 400) = -Real.log (400 / 489) := by
    rw [show ((489 / 400) : ℝ) = ((400 / 489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7586_neg : (125835817 / 500000000) ≤ -Real.log (311 / 400) ∧
    -Real.log (311 / 400) ≤ (50334327 / 200000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 311) = 1/(311 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7586 : Bounds (-50334327 / 200000000) (-125835817 / 500000000) (Real.log (311 / 400)) := by
  have h := reflection_log_7586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7587_neg : (8899 / 40000000) ≤ -Real.log (400000 / 400089) ∧
    -Real.log (400000 / 400089) ≤ (55619 / 250000000) := by
  have h := checkLog_sound (w := (89 / 800089)) (n := 12)
    (lo := (8899 / 40000000)) (hi := (55619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400089 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400089 / 400000) = 1/(400000 / 400089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7587 : Bounds (8899 / 40000000) (55619 / 250000000) (Real.log (400089 / 400000)) := by
  have h := reflection_log_7587_neg
  have he : Real.log (400089 / 400000) = -Real.log (400000 / 400089) := by
    rw [show ((400089 / 400000) : ℝ) = ((400000 / 400089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7588_neg : (55631 / 250000000) ≤ -Real.log (399911 / 400000) ∧
    -Real.log (399911 / 400000) ≤ (8901 / 40000000) := by
  have h := checkLog_sound (w := (89 / 799911)) (n := 12)
    (lo := (55631 / 250000000)) (hi := (8901 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399911) = 1/(399911 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7588 : Bounds (-8901 / 40000000) (-55631 / 250000000) (Real.log (399911 / 400000)) := by
  have h := reflection_log_7588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7589_neg : (106062169 / 1000000000) ≤ -Real.log (1000000 / 1111891) ∧
    -Real.log (1000000 / 1111891) ≤ (10606217 / 100000000) := by
  have h := checkLog_sound (w := (111891 / 2111891)) (n := 12)
    (lo := (106062169 / 1000000000)) (hi := (10606217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111891 / 1000000) = 1/(1000000 / 1111891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7589 : Bounds (106062169 / 1000000000) (10606217 / 100000000) (Real.log (1111891 / 1000000)) := by
  have h := reflection_log_7589_neg
  have he : Real.log (1111891 / 1000000) = -Real.log (1000000 / 1111891) := by
    rw [show ((1111891 / 1000000) : ℝ) = ((1000000 / 1111891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7590_neg : (23732159 / 200000000) ≤ -Real.log (888109 / 1000000) ∧
    -Real.log (888109 / 1000000) ≤ (29665199 / 250000000) := by
  have h := checkLog_sound (w := (111891 / 1888109)) (n := 12)
    (lo := (23732159 / 200000000)) (hi := (29665199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888109) = 1/(888109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7590 : Bounds (-29665199 / 250000000) (-23732159 / 200000000) (Real.log (888109 / 1000000)) := by
  have h := reflection_log_7590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7591_neg : (4259679 / 40000000) ≤ -Real.log (1000000 / 1112369) ∧
    -Real.log (1000000 / 1112369) ≤ (13311497 / 125000000) := by
  have h := checkLog_sound (w := (112369 / 2112369)) (n := 12)
    (lo := (4259679 / 40000000)) (hi := (13311497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112369 / 1000000) = 1/(1000000 / 1112369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7591 : Bounds (4259679 / 40000000) (13311497 / 125000000) (Real.log (1112369 / 1000000)) := by
  have h := reflection_log_7591_neg
  have he : Real.log (1112369 / 1000000) = -Real.log (1000000 / 1112369) := by
    rw [show ((1112369 / 1000000) : ℝ) = ((1000000 / 1112369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7592_neg : (59599581 / 500000000) ≤ -Real.log (887631 / 1000000) ∧
    -Real.log (887631 / 1000000) ≤ (119199163 / 1000000000) := by
  have h := checkLog_sound (w := (112369 / 1887631)) (n := 12)
    (lo := (59599581 / 500000000)) (hi := (119199163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887631) = 1/(887631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7592 : Bounds (-119199163 / 1000000000) (-59599581 / 500000000) (Real.log (887631 / 1000000)) := by
  have h := reflection_log_7592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7593_neg : (12707187 / 1000000000) ≤ -Real.log (987373207839 / 1000000000000) ∧
    -Real.log (987373207839 / 1000000000000) ≤ (3176797 / 250000000) := by
  have h := checkLog_sound (w := (12626792161 / 1987373207839)) (n := 12)
    (lo := (12707187 / 1000000000)) (hi := (3176797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987373207839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987373207839) = 1/(987373207839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7593 : Bounds (-3176797 / 250000000) (-12707187 / 1000000000) (Real.log (987373207839 / 1000000000000)) := by
  have h := reflection_log_7593_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7594_neg : (6299313 / 500000000) ≤ -Real.log (987480404119 / 1000000000000) ∧
    -Real.log (987480404119 / 1000000000000) ≤ (12598627 / 1000000000) := by
  have h := checkLog_sound (w := (12519595881 / 1987480404119)) (n := 12)
    (lo := (6299313 / 500000000)) (hi := (12598627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987480404119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987480404119) = 1/(987480404119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7594 : Bounds (-12598627 / 1000000000) (-6299313 / 500000000) (Real.log (987480404119 / 1000000000000)) := by
  have h := reflection_log_7594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7595_neg : (44944593 / 200000000) ≤ -Real.log (100000000000 / 125197582729) ∧
    -Real.log (100000000000 / 125197582729) ≤ (112361483 / 500000000) := by
  have h := checkLog_sound (w := (25197582729 / 225197582729)) (n := 12)
    (lo := (44944593 / 200000000)) (hi := (112361483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125197582729 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125197582729 / 100000000000) = 1/(100000000000 / 125197582729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7595 : Bounds (44944593 / 200000000) (112361483 / 500000000) (Real.log (125197582729 / 100000000000)) := by
  have h := reflection_log_7595_neg
  have he : Real.log (125197582729 / 100000000000) = -Real.log (100000000000 / 125197582729) := by
    rw [show ((125197582729 / 100000000000) : ℝ) = ((100000000000 / 125197582729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7596_neg : (112845569 / 500000000) ≤ -Real.log (500000000000 / 626594271719) ∧
    -Real.log (500000000000 / 626594271719) ≤ (225691139 / 1000000000) := by
  have h := checkLog_sound (w := (126594271719 / 1126594271719)) (n := 12)
    (lo := (112845569 / 500000000)) (hi := (225691139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626594271719 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626594271719 / 500000000000) = 1/(500000000000 / 626594271719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7596 : Bounds (112845569 / 500000000) (225691139 / 1000000000) (Real.log (626594271719 / 500000000000)) := by
  have h := reflection_log_7596_neg
  have he : Real.log (626594271719 / 500000000000) = -Real.log (500000000000 / 626594271719) := by
    rw [show ((626594271719 / 500000000000) : ℝ) = ((500000000000 / 626594271719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7597_neg : (90303523 / 200000000) ≤ -Real.log (500000000000 / 785347043701) ∧
    -Real.log (500000000000 / 785347043701) ≤ (28219851 / 62500000) := by
  have h := checkLog_sound (w := (285347043701 / 1285347043701)) (n := 12)
    (lo := (90303523 / 200000000)) (hi := (28219851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785347043701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785347043701 / 500000000000) = 1/(500000000000 / 785347043701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7597 : Bounds (90303523 / 200000000) (28219851 / 62500000) (Real.log (785347043701 / 500000000000)) := by
  have h := reflection_log_7597_neg
  have he : Real.log (785347043701 / 500000000000) = -Real.log (500000000000 / 785347043701) := by
    rw [show ((785347043701 / 500000000000) : ℝ) = ((500000000000 / 785347043701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7598_neg : (452569577 / 1000000000) ≤ -Real.log (500000000000 / 786173633441) ∧
    -Real.log (500000000000 / 786173633441) ≤ (226284789 / 500000000) := by
  have h := checkLog_sound (w := (286173633441 / 1286173633441)) (n := 12)
    (lo := (452569577 / 1000000000)) (hi := (226284789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786173633441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786173633441 / 500000000000) = 1/(500000000000 / 786173633441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7598 : Bounds (452569577 / 1000000000) (226284789 / 500000000) (Real.log (786173633441 / 500000000000)) := by
  have h := reflection_log_7598_neg
  have he : Real.log (786173633441 / 500000000000) = -Real.log (500000000000 / 786173633441) := by
    rw [show ((786173633441 / 500000000000) : ℝ) = ((500000000000 / 786173633441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7599_neg : (25163357 / 125000000) ≤ -Real.log (1000 / 1223) ∧
    -Real.log (1000 / 1223) ≤ (201306857 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2223)) (n := 12)
    (lo := (25163357 / 125000000)) (hi := (201306857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 1000) = 1/(1000 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7599 : Bounds (25163357 / 125000000) (201306857 / 1000000000) (Real.log (1223 / 1000)) := by
  have h := reflection_log_7599_neg
  have he : Real.log (1223 / 1000) = -Real.log (1000 / 1223) := by
    rw [show ((1223 / 1000) : ℝ) = ((1000 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7600_neg : (15769683 / 62500000) ≤ -Real.log (777 / 1000) ∧
    -Real.log (777 / 1000) ≤ (252314929 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1777)) (n := 12)
    (lo := (15769683 / 62500000)) (hi := (252314929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 777) = 1/(777 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7600 : Bounds (-252314929 / 1000000000) (-15769683 / 62500000) (Real.log (777 / 1000)) := by
  have h := reflection_log_7600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7601_neg : (8919 / 40000000) ≤ -Real.log (1000000 / 1000223) ∧
    -Real.log (1000000 / 1000223) ≤ (871 / 3906250) := by
  have h := checkLog_sound (w := (223 / 2000223)) (n := 12)
    (lo := (8919 / 40000000)) (hi := (871 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000223 / 1000000) = 1/(1000000 / 1000223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7601 : Bounds (8919 / 40000000) (871 / 3906250) (Real.log (1000223 / 1000000)) := by
  have h := reflection_log_7601_neg
  have he : Real.log (1000223 / 1000000) = -Real.log (1000000 / 1000223) := by
    rw [show ((1000223 / 1000000) : ℝ) = ((1000000 / 1000223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7602_neg : (13939 / 62500000) ≤ -Real.log (999777 / 1000000) ∧
    -Real.log (999777 / 1000000) ≤ (8921 / 40000000) := by
  have h := checkLog_sound (w := (223 / 1999777)) (n := 12)
    (lo := (13939 / 62500000)) (hi := (8921 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999777) = 1/(999777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7602 : Bounds (-8921 / 40000000) (-13939 / 62500000) (Real.log (999777 / 1000000)) := by
  have h := reflection_log_7602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7603_neg : (106292381 / 1000000000) ≤ -Real.log (1000000 / 1112147) ∧
    -Real.log (1000000 / 1112147) ≤ (53146191 / 500000000) := by
  have h := checkLog_sound (w := (112147 / 2112147)) (n := 12)
    (lo := (106292381 / 1000000000)) (hi := (53146191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112147 / 1000000) = 1/(1000000 / 1112147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7603 : Bounds (106292381 / 1000000000) (53146191 / 500000000) (Real.log (1112147 / 1000000)) := by
  have h := reflection_log_7603_neg
  have he : Real.log (1112147 / 1000000) = -Real.log (1000000 / 1112147) := by
    rw [show ((1112147 / 1000000) : ℝ) = ((1000000 / 1112147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7604_neg : (11894909 / 100000000) ≤ -Real.log (887853 / 1000000) ∧
    -Real.log (887853 / 1000000) ≤ (118949091 / 1000000000) := by
  have h := checkLog_sound (w := (112147 / 1887853)) (n := 12)
    (lo := (11894909 / 100000000)) (hi := (118949091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887853) = 1/(887853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7604 : Bounds (-118949091 / 1000000000) (-11894909 / 100000000) (Real.log (887853 / 1000000)) := by
  have h := reflection_log_7604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7605_neg : (106722987 / 1000000000) ≤ -Real.log (500000 / 556313) ∧
    -Real.log (500000 / 556313) ≤ (26680747 / 250000000) := by
  have h := checkLog_sound (w := (56313 / 1056313)) (n := 12)
    (lo := (106722987 / 1000000000)) (hi := (26680747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556313 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(556313 / 500000) = 1/(500000 / 556313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7605 : Bounds (106722987 / 1000000000) (26680747 / 250000000) (Real.log (556313 / 500000)) := by
  have h := reflection_log_7605_neg
  have he : Real.log (556313 / 500000) = -Real.log (500000 / 556313) := by
    rw [show ((556313 / 500000) : ℝ) = ((500000 / 556313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7606_neg : (119488739 / 1000000000) ≤ -Real.log (443687 / 500000) ∧
    -Real.log (443687 / 500000) ≤ (5974437 / 50000000) := by
  have h := checkLog_sound (w := (56313 / 943687)) (n := 12)
    (lo := (119488739 / 1000000000)) (hi := (5974437 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 443687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 443687) = 1/(443687 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7606 : Bounds (-5974437 / 50000000) (-119488739 / 1000000000) (Real.log (443687 / 500000)) := by
  have h := reflection_log_7606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7607_neg : (1595719 / 125000000) ≤ -Real.log (246828846031 / 250000000000) ∧
    -Real.log (246828846031 / 250000000000) ≤ (12765753 / 1000000000) := by
  have h := checkLog_sound (w := (3171153969 / 496828846031)) (n := 12)
    (lo := (1595719 / 125000000)) (hi := (12765753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246828846031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246828846031) = 1/(246828846031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7607 : Bounds (-12765753 / 1000000000) (-1595719 / 125000000) (Real.log (246828846031 / 250000000000)) := by
  have h := reflection_log_7607_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7608_neg : (3164177 / 250000000) ≤ -Real.log (987423050391 / 1000000000000) ∧
    -Real.log (987423050391 / 1000000000000) ≤ (12656709 / 1000000000) := by
  have h := checkLog_sound (w := (12576949609 / 1987423050391)) (n := 12)
    (lo := (3164177 / 250000000)) (hi := (12656709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987423050391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987423050391) = 1/(987423050391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7608 : Bounds (-12656709 / 1000000000) (-3164177 / 250000000) (Real.log (987423050391 / 1000000000000)) := by
  have h := reflection_log_7608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7609_neg : (225241471 / 1000000000) ≤ -Real.log (250000000000 / 313156288259) ∧
    -Real.log (250000000000 / 313156288259) ≤ (1759699 / 7812500) := by
  have h := checkLog_sound (w := (63156288259 / 563156288259)) (n := 12)
    (lo := (225241471 / 1000000000)) (hi := (1759699 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313156288259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313156288259 / 250000000000) = 1/(250000000000 / 313156288259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7609 : Bounds (225241471 / 1000000000) (1759699 / 7812500) (Real.log (313156288259 / 250000000000)) := by
  have h := reflection_log_7609_neg
  have he : Real.log (313156288259 / 250000000000) = -Real.log (250000000000 / 313156288259) := by
    rw [show ((313156288259 / 250000000000) : ℝ) = ((250000000000 / 313156288259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7610_neg : (113105863 / 500000000) ≤ -Real.log (100000000000 / 125384110871) ∧
    -Real.log (100000000000 / 125384110871) ≤ (226211727 / 1000000000) := by
  have h := checkLog_sound (w := (25384110871 / 225384110871)) (n := 12)
    (lo := (113105863 / 500000000)) (hi := (226211727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125384110871 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125384110871 / 100000000000) = 1/(100000000000 / 125384110871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7610 : Bounds (113105863 / 500000000) (226211727 / 1000000000) (Real.log (125384110871 / 100000000000)) := by
  have h := reflection_log_7610_neg
  have he : Real.log (125384110871 / 100000000000) = -Real.log (100000000000 / 125384110871) := by
    rw [show ((125384110871 / 100000000000) : ℝ) = ((100000000000 / 125384110871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7611_neg : (452569577 / 1000000000) ≤ -Real.log (3125000000 / 4913585209) ∧
    -Real.log (3125000000 / 4913585209) ≤ (226284789 / 500000000) := by
  have h := checkLog_sound (w := (1788585209 / 8038585209)) (n := 12)
    (lo := (452569577 / 1000000000)) (hi := (226284789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4913585209 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4913585209 / 3125000000) = 1/(3125000000 / 4913585209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7611 : Bounds (452569577 / 1000000000) (226284789 / 500000000) (Real.log (4913585209 / 3125000000)) := by
  have h := reflection_log_7611_neg
  have he : Real.log (4913585209 / 3125000000) = -Real.log (3125000000 / 4913585209) := by
    rw [show ((4913585209 / 3125000000) : ℝ) = ((3125000000 / 4913585209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7612_neg : (90724357 / 200000000) ≤ -Real.log (250000000000 / 393500643501) ∧
    -Real.log (250000000000 / 393500643501) ≤ (226810893 / 500000000) := by
  have h := checkLog_sound (w := (143500643501 / 643500643501)) (n := 12)
    (lo := (90724357 / 200000000)) (hi := (226810893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393500643501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393500643501 / 250000000000) = 1/(250000000000 / 393500643501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7612 : Bounds (90724357 / 200000000) (226810893 / 500000000) (Real.log (393500643501 / 250000000000)) := by
  have h := reflection_log_7612_neg
  have he : Real.log (393500643501 / 250000000000) = -Real.log (250000000000 / 393500643501) := by
    rw [show ((393500643501 / 250000000000) : ℝ) = ((250000000000 / 393500643501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7613_neg : (201715603 / 1000000000) ≤ -Real.log (2000 / 2447) ∧
    -Real.log (2000 / 2447) ≤ (50428901 / 250000000) := by
  have h := checkLog_sound (w := (447 / 4447)) (n := 12)
    (lo := (201715603 / 1000000000)) (hi := (50428901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2447 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2447 / 2000) = 1/(2000 / 2447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7613 : Bounds (201715603 / 1000000000) (50428901 / 250000000) (Real.log (2447 / 2000)) := by
  have h := reflection_log_7613_neg
  have he : Real.log (2447 / 2000) = -Real.log (2000 / 2447) := by
    rw [show ((2447 / 2000) : ℝ) = ((2000 / 2447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7614_neg : (63239659 / 250000000) ≤ -Real.log (1553 / 2000) ∧
    -Real.log (1553 / 2000) ≤ (252958637 / 1000000000) := by
  have h := checkLog_sound (w := (447 / 3553)) (n := 12)
    (lo := (63239659 / 250000000)) (hi := (252958637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1553) = 1/(1553 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7614 : Bounds (-252958637 / 1000000000) (-63239659 / 250000000) (Real.log (1553 / 2000)) := by
  have h := reflection_log_7614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7615_neg : (8939 / 40000000) ≤ -Real.log (2000000 / 2000447) ∧
    -Real.log (2000000 / 2000447) ≤ (55869 / 250000000) := by
  have h := checkLog_sound (w := (447 / 4000447)) (n := 12)
    (lo := (8939 / 40000000)) (hi := (55869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000447 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000447 / 2000000) = 1/(2000000 / 2000447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7615 : Bounds (8939 / 40000000) (55869 / 250000000) (Real.log (2000447 / 2000000)) := by
  have h := reflection_log_7615_neg
  have he : Real.log (2000447 / 2000000) = -Real.log (2000000 / 2000447) := by
    rw [show ((2000447 / 2000000) : ℝ) = ((2000000 / 2000447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0119 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7616_neg : (55881 / 250000000) ≤ -Real.log (1999553 / 2000000) ∧
    -Real.log (1999553 / 2000000) ≤ (8941 / 40000000) := by
  have h := checkLog_sound (w := (447 / 3999553)) (n := 12)
    (lo := (55881 / 250000000)) (hi := (8941 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999553) = 1/(1999553 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7616 : Bounds (-8941 / 40000000) (-55881 / 250000000) (Real.log (1999553 / 2000000)) := by
  have h := reflection_log_7616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7617_neg : (106523439 / 1000000000) ≤ -Real.log (250000 / 278101) ∧
    -Real.log (250000 / 278101) ≤ (1331543 / 12500000) := by
  have h := checkLog_sound (w := (28101 / 528101)) (n := 12)
    (lo := (106523439 / 1000000000)) (hi := (1331543 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278101 / 250000) = 1/(250000 / 278101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7617 : Bounds (106523439 / 1000000000) (1331543 / 12500000) (Real.log (278101 / 250000)) := by
  have h := reflection_log_7617_neg
  have he : Real.log (278101 / 250000) = -Real.log (250000 / 278101) := by
    rw [show ((278101 / 250000) : ℝ) = ((250000 / 278101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7618_neg : (59619297 / 500000000) ≤ -Real.log (221899 / 250000) ∧
    -Real.log (221899 / 250000) ≤ (23847719 / 200000000) := by
  have h := checkLog_sound (w := (28101 / 471899)) (n := 12)
    (lo := (59619297 / 500000000)) (hi := (23847719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 221899) = 1/(221899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7618 : Bounds (-23847719 / 200000000) (-59619297 / 500000000) (Real.log (221899 / 250000)) := by
  have h := reflection_log_7618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7619_neg : (21390789 / 200000000) ≤ -Real.log (1000000 / 1112883) ∧
    -Real.log (1000000 / 1112883) ≤ (53476973 / 500000000) := by
  have h := checkLog_sound (w := (112883 / 2112883)) (n := 12)
    (lo := (21390789 / 200000000)) (hi := (53476973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112883 / 1000000) = 1/(1000000 / 1112883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7619 : Bounds (21390789 / 200000000) (53476973 / 500000000) (Real.log (1112883 / 1000000)) := by
  have h := reflection_log_7619_neg
  have he : Real.log (1112883 / 1000000) = -Real.log (1000000 / 1112883) := by
    rw [show ((1112883 / 1000000) : ℝ) = ((1000000 / 1112883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7620_neg : (149723 / 1250000) ≤ -Real.log (887117 / 1000000) ∧
    -Real.log (887117 / 1000000) ≤ (119778401 / 1000000000) := by
  have h := checkLog_sound (w := (112883 / 1887117)) (n := 12)
    (lo := (149723 / 1250000)) (hi := (119778401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887117) = 1/(887117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7620 : Bounds (-119778401 / 1000000000) (-149723 / 1250000) (Real.log (887117 / 1000000)) := by
  have h := reflection_log_7620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7621_neg : (6412227 / 500000000) ≤ -Real.log (987257428311 / 1000000000000) ∧
    -Real.log (987257428311 / 1000000000000) ≤ (2564891 / 200000000) := by
  have h := checkLog_sound (w := (12742571689 / 1987257428311)) (n := 12)
    (lo := (6412227 / 500000000)) (hi := (2564891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987257428311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987257428311) = 1/(987257428311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7621 : Bounds (-2564891 / 200000000) (-6412227 / 500000000) (Real.log (987257428311 / 1000000000000)) := by
  have h := reflection_log_7621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7622_neg : (2543031 / 200000000) ≤ -Real.log (61710333799 / 62500000000) ∧
    -Real.log (61710333799 / 62500000000) ≤ (3178789 / 250000000) := by
  have h := checkLog_sound (w := (789666201 / 124210333799)) (n := 12)
    (lo := (2543031 / 200000000)) (hi := (3178789 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61710333799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61710333799) = 1/(61710333799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7622 : Bounds (-3178789 / 250000000) (-2543031 / 200000000) (Real.log (61710333799 / 62500000000)) := by
  have h := reflection_log_7622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7623_neg : (225762033 / 1000000000) ≤ -Real.log (500000000000 / 626638695983) ∧
    -Real.log (500000000000 / 626638695983) ≤ (112881017 / 500000000) := by
  have h := checkLog_sound (w := (126638695983 / 1126638695983)) (n := 12)
    (lo := (225762033 / 1000000000)) (hi := (112881017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626638695983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626638695983 / 500000000000) = 1/(500000000000 / 626638695983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7623 : Bounds (225762033 / 1000000000) (112881017 / 500000000) (Real.log (626638695983 / 500000000000)) := by
  have h := reflection_log_7623_neg
  have he : Real.log (626638695983 / 500000000000) = -Real.log (500000000000 / 626638695983) := by
    rw [show ((626638695983 / 500000000000) : ℝ) = ((500000000000 / 626638695983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7624_neg : (45346469 / 200000000) ≤ -Real.log (500000000000 / 627247026041) ∧
    -Real.log (500000000000 / 627247026041) ≤ (113366173 / 500000000) := by
  have h := checkLog_sound (w := (127247026041 / 1127247026041)) (n := 12)
    (lo := (45346469 / 200000000)) (hi := (113366173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627247026041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627247026041 / 500000000000) = 1/(500000000000 / 627247026041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7624 : Bounds (45346469 / 200000000) (113366173 / 500000000) (Real.log (627247026041 / 500000000000)) := by
  have h := reflection_log_7624_neg
  have he : Real.log (627247026041 / 500000000000) = -Real.log (500000000000 / 627247026041) := by
    rw [show ((627247026041 / 500000000000) : ℝ) = ((500000000000 / 627247026041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7625_neg : (90724357 / 200000000) ≤ -Real.log (500000000000 / 787001287001) ∧
    -Real.log (500000000000 / 787001287001) ≤ (226810893 / 500000000) := by
  have h := checkLog_sound (w := (287001287001 / 1287001287001)) (n := 12)
    (lo := (90724357 / 200000000)) (hi := (226810893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787001287001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787001287001 / 500000000000) = 1/(500000000000 / 787001287001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7625 : Bounds (90724357 / 200000000) (226810893 / 500000000) (Real.log (787001287001 / 500000000000)) := by
  have h := reflection_log_7625_neg
  have he : Real.log (787001287001 / 500000000000) = -Real.log (500000000000 / 787001287001) := by
    rw [show ((787001287001 / 500000000000) : ℝ) = ((500000000000 / 787001287001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7626_neg : (1420857 / 3125000) ≤ -Real.log (12500000000 / 19695750161) ∧
    -Real.log (12500000000 / 19695750161) ≤ (454674241 / 1000000000) := by
  have h := checkLog_sound (w := (7195750161 / 32195750161)) (n := 12)
    (lo := (1420857 / 3125000)) (hi := (454674241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19695750161 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19695750161 / 12500000000) = 1/(12500000000 / 19695750161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7626 : Bounds (1420857 / 3125000) (454674241 / 1000000000) (Real.log (19695750161 / 12500000000)) := by
  have h := reflection_log_7626_neg
  have he : Real.log (19695750161 / 12500000000) = -Real.log (12500000000 / 19695750161) := by
    rw [show ((19695750161 / 12500000000) : ℝ) = ((12500000000 / 19695750161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7627_neg : (25265523 / 125000000) ≤ -Real.log (125 / 153) ∧
    -Real.log (125 / 153) ≤ (40424837 / 200000000) := by
  have h := checkLog_sound (w := (14 / 139)) (n := 12)
    (lo := (25265523 / 125000000)) (hi := (40424837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 125) = 1/(125 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7627 : Bounds (25265523 / 125000000) (40424837 / 200000000) (Real.log (153 / 125)) := by
  have h := reflection_log_7627_neg
  have he : Real.log (153 / 125) = -Real.log (125 / 153) := by
    rw [show ((153 / 125) : ℝ) = ((125 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7628_neg : (126801379 / 500000000) ≤ -Real.log (97 / 125) ∧
    -Real.log (97 / 125) ≤ (253602759 / 1000000000) := by
  have h := checkLog_sound (w := (14 / 111)) (n := 12)
    (lo := (126801379 / 500000000)) (hi := (253602759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 97) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 97) = 1/(97 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7628 : Bounds (-253602759 / 1000000000) (-126801379 / 500000000) (Real.log (97 / 125)) := by
  have h := reflection_log_7628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7629_neg : (111987 / 500000000) ≤ -Real.log (31250 / 31257) ∧
    -Real.log (31250 / 31257) ≤ (8959 / 40000000) := by
  have h := checkLog_sound (w := (7 / 62507)) (n := 12)
    (lo := (111987 / 500000000)) (hi := (8959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31257 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31257 / 31250) = 1/(31250 / 31257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7629 : Bounds (111987 / 500000000) (8959 / 40000000) (Real.log (31257 / 31250)) := by
  have h := reflection_log_7629_neg
  have he : Real.log (31257 / 31250) = -Real.log (31250 / 31257) := by
    rw [show ((31257 / 31250) : ℝ) = ((31250 / 31257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7630_neg : (8961 / 40000000) ≤ -Real.log (31243 / 31250) ∧
    -Real.log (31243 / 31250) ≤ (112013 / 500000000) := by
  have h := checkLog_sound (w := (7 / 62493)) (n := 12)
    (lo := (8961 / 40000000)) (hi := (112013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31243) = 1/(31243 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7630 : Bounds (-112013 / 500000000) (-8961 / 40000000) (Real.log (31243 / 31250)) := by
  have h := reflection_log_7630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7631_neg : (13344193 / 125000000) ≤ -Real.log (50000 / 55633) ∧
    -Real.log (50000 / 55633) ≤ (21350709 / 200000000) := by
  have h := checkLog_sound (w := (5633 / 105633)) (n := 12)
    (lo := (13344193 / 125000000)) (hi := (21350709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55633 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55633 / 50000) = 1/(50000 / 55633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7631 : Bounds (13344193 / 125000000) (21350709 / 200000000) (Real.log (55633 / 50000)) := by
  have h := reflection_log_7631_neg
  have he : Real.log (55633 / 50000) = -Real.log (50000 / 55633) := by
    rw [show ((55633 / 50000) : ℝ) = ((50000 / 55633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7632_neg : (23905411 / 200000000) ≤ -Real.log (44367 / 50000) ∧
    -Real.log (44367 / 50000) ≤ (7470441 / 62500000) := by
  have h := checkLog_sound (w := (5633 / 94367)) (n := 12)
    (lo := (23905411 / 200000000)) (hi := (7470441 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44367) = 1/(44367 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7632 : Bounds (-7470441 / 62500000) (-23905411 / 200000000) (Real.log (44367 / 50000)) := by
  have h := reflection_log_7632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7633_neg : (2143697 / 20000000) ≤ -Real.log (50000 / 55657) ∧
    -Real.log (50000 / 55657) ≤ (107184851 / 1000000000) := by
  have h := checkLog_sound (w := (5657 / 105657)) (n := 12)
    (lo := (2143697 / 20000000)) (hi := (107184851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55657 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55657 / 50000) = 1/(50000 / 55657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7633 : Bounds (2143697 / 20000000) (107184851 / 1000000000) (Real.log (55657 / 50000)) := by
  have h := reflection_log_7633_neg
  have he : Real.log (55657 / 50000) = -Real.log (50000 / 55657) := by
    rw [show ((55657 / 50000) : ℝ) = ((50000 / 55657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7634_neg : (7504259 / 62500000) ≤ -Real.log (44343 / 50000) ∧
    -Real.log (44343 / 50000) ≤ (24013629 / 200000000) := by
  have h := checkLog_sound (w := (5657 / 94343)) (n := 12)
    (lo := (7504259 / 62500000)) (hi := (24013629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44343) = 1/(44343 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7634 : Bounds (-24013629 / 200000000) (-7504259 / 62500000) (Real.log (44343 / 50000)) := by
  have h := reflection_log_7634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7635_neg : (12883293 / 1000000000) ≤ -Real.log (2467998351 / 2500000000) ∧
    -Real.log (2467998351 / 2500000000) ≤ (6441647 / 500000000) := by
  have h := checkLog_sound (w := (32001649 / 4967998351)) (n := 12)
    (lo := (12883293 / 1000000000)) (hi := (6441647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2467998351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2467998351) = 1/(2467998351 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7635 : Bounds (-6441647 / 500000000) (-12883293 / 1000000000) (Real.log (2467998351 / 2500000000)) := by
  have h := reflection_log_7635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7636_neg : (1277351 / 100000000) ≤ -Real.log (2468269311 / 2500000000) ∧
    -Real.log (2468269311 / 2500000000) ≤ (12773511 / 1000000000) := by
  have h := checkLog_sound (w := (31730689 / 4968269311)) (n := 12)
    (lo := (1277351 / 100000000)) (hi := (12773511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2468269311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2468269311) = 1/(2468269311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7636 : Bounds (-12773511 / 1000000000) (-1277351 / 100000000) (Real.log (2468269311 / 2500000000)) := by
  have h := reflection_log_7636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7637_neg : (1131403 / 5000000) ≤ -Real.log (500000000000 / 626963734307) ∧
    -Real.log (500000000000 / 626963734307) ≤ (226280601 / 1000000000) := by
  have h := checkLog_sound (w := (126963734307 / 1126963734307)) (n := 12)
    (lo := (1131403 / 5000000)) (hi := (226280601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626963734307 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626963734307 / 500000000000) = 1/(500000000000 / 626963734307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7637 : Bounds (1131403 / 5000000) (226280601 / 1000000000) (Real.log (626963734307 / 500000000000)) := by
  have h := reflection_log_7637_neg
  have he : Real.log (626963734307 / 500000000000) = -Real.log (500000000000 / 626963734307) := by
    rw [show ((626963734307 / 500000000000) : ℝ) = ((500000000000 / 626963734307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7638_neg : (45450599 / 200000000) ≤ -Real.log (500000000000 / 627573686941) ∧
    -Real.log (500000000000 / 627573686941) ≤ (56813249 / 250000000) := by
  have h := checkLog_sound (w := (127573686941 / 1127573686941)) (n := 12)
    (lo := (45450599 / 200000000)) (hi := (56813249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627573686941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627573686941 / 500000000000) = 1/(500000000000 / 627573686941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7638 : Bounds (45450599 / 200000000) (56813249 / 250000000) (Real.log (627573686941 / 500000000000)) := by
  have h := reflection_log_7638_neg
  have he : Real.log (627573686941 / 500000000000) = -Real.log (500000000000 / 627573686941) := by
    rw [show ((627573686941 / 500000000000) : ℝ) = ((500000000000 / 627573686941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7639_neg : (1420857 / 3125000) ≤ -Real.log (500000000000 / 787830006439) ∧
    -Real.log (500000000000 / 787830006439) ≤ (454674241 / 1000000000) := by
  have h := checkLog_sound (w := (287830006439 / 1287830006439)) (n := 12)
    (lo := (1420857 / 3125000)) (hi := (454674241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787830006439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787830006439 / 500000000000) = 1/(500000000000 / 787830006439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7639 : Bounds (1420857 / 3125000) (454674241 / 1000000000) (Real.log (787830006439 / 500000000000)) := by
  have h := reflection_log_7639_neg
  have he : Real.log (787830006439 / 500000000000) = -Real.log (500000000000 / 787830006439) := by
    rw [show ((787830006439 / 500000000000) : ℝ) = ((500000000000 / 787830006439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7640_neg : (227863471 / 500000000) ≤ -Real.log (100000000000 / 157731958763) ∧
    -Real.log (100000000000 / 157731958763) ≤ (455726943 / 1000000000) := by
  have h := checkLog_sound (w := (57731958763 / 257731958763)) (n := 12)
    (lo := (227863471 / 500000000)) (hi := (455726943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157731958763 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157731958763 / 100000000000) = 1/(100000000000 / 157731958763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7640 : Bounds (227863471 / 500000000) (455726943 / 1000000000) (Real.log (157731958763 / 100000000000)) := by
  have h := reflection_log_7640_neg
  have he : Real.log (157731958763 / 100000000000) = -Real.log (100000000000 / 157731958763) := by
    rw [show ((157731958763 / 100000000000) : ℝ) = ((100000000000 / 157731958763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7641_neg : (202532597 / 1000000000) ≤ -Real.log (2000 / 2449) ∧
    -Real.log (2000 / 2449) ≤ (101266299 / 500000000) := by
  have h := checkLog_sound (w := (449 / 4449)) (n := 12)
    (lo := (202532597 / 1000000000)) (hi := (101266299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2449 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2449 / 2000) = 1/(2000 / 2449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7641 : Bounds (202532597 / 1000000000) (101266299 / 500000000) (Real.log (2449 / 2000)) := by
  have h := reflection_log_7641_neg
  have he : Real.log (2449 / 2000) = -Real.log (2000 / 2449) := by
    rw [show ((2449 / 2000) : ℝ) = ((2000 / 2449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7642_neg : (1986307 / 7812500) ≤ -Real.log (1551 / 2000) ∧
    -Real.log (1551 / 2000) ≤ (254247297 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 3551)) (n := 12)
    (lo := (1986307 / 7812500)) (hi := (254247297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1551) = 1/(1551 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7642 : Bounds (-254247297 / 1000000000) (-1986307 / 7812500) (Real.log (1551 / 2000)) := by
  have h := reflection_log_7642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7643_neg : (112237 / 500000000) ≤ -Real.log (2000000 / 2000449) ∧
    -Real.log (2000000 / 2000449) ≤ (8979 / 40000000) := by
  have h := checkLog_sound (w := (449 / 4000449)) (n := 12)
    (lo := (112237 / 500000000)) (hi := (8979 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000449 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000449 / 2000000) = 1/(2000000 / 2000449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7643 : Bounds (112237 / 500000000) (8979 / 40000000) (Real.log (2000449 / 2000000)) := by
  have h := reflection_log_7643_neg
  have he : Real.log (2000449 / 2000000) = -Real.log (2000000 / 2000449) := by
    rw [show ((2000449 / 2000000) : ℝ) = ((2000000 / 2000449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7644_neg : (8981 / 40000000) ≤ -Real.log (1999551 / 2000000) ∧
    -Real.log (1999551 / 2000000) ≤ (112263 / 500000000) := by
  have h := checkLog_sound (w := (449 / 3999551)) (n := 12)
    (lo := (8981 / 40000000)) (hi := (112263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999551) = 1/(1999551 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7644 : Bounds (-112263 / 500000000) (-8981 / 40000000) (Real.log (1999551 / 2000000)) := by
  have h := reflection_log_7644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7645_neg : (6686531 / 62500000) ≤ -Real.log (1000000 / 1112917) ∧
    -Real.log (1000000 / 1112917) ≤ (106984497 / 1000000000) := by
  have h := checkLog_sound (w := (112917 / 2112917)) (n := 12)
    (lo := (6686531 / 62500000)) (hi := (106984497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112917 / 1000000) = 1/(1000000 / 1112917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7645 : Bounds (6686531 / 62500000) (106984497 / 1000000000) (Real.log (1112917 / 1000000)) := by
  have h := reflection_log_7645_neg
  have he : Real.log (1112917 / 1000000) = -Real.log (1000000 / 1112917) := by
    rw [show ((1112917 / 1000000) : ℝ) = ((1000000 / 1112917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7646_neg : (119816727 / 1000000000) ≤ -Real.log (887083 / 1000000) ∧
    -Real.log (887083 / 1000000) ≤ (14977091 / 125000000) := by
  have h := checkLog_sound (w := (112917 / 1887083)) (n := 12)
    (lo := (119816727 / 1000000000)) (hi := (14977091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887083) = 1/(887083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7646 : Bounds (-14977091 / 125000000) (-119816727 / 1000000000) (Real.log (887083 / 1000000)) := by
  have h := reflection_log_7646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7647_neg : (53707851 / 500000000) ≤ -Real.log (1000000 / 1113397) ∧
    -Real.log (1000000 / 1113397) ≤ (107415703 / 1000000000) := by
  have h := checkLog_sound (w := (113397 / 2113397)) (n := 12)
    (lo := (53707851 / 500000000)) (hi := (107415703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113397 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1113397 / 1000000) = 1/(1000000 / 1113397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7647 : Bounds (53707851 / 500000000) (107415703 / 1000000000) (Real.log (1113397 / 1000000)) := by
  have h := reflection_log_7647_neg
  have he : Real.log (1113397 / 1000000) = -Real.log (1000000 / 1113397) := by
    rw [show ((1113397 / 1000000) : ℝ) = ((1000000 / 1113397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7648_neg : (30089493 / 250000000) ≤ -Real.log (886603 / 1000000) ∧
    -Real.log (886603 / 1000000) ≤ (120357973 / 1000000000) := by
  have h := checkLog_sound (w := (113397 / 1886603)) (n := 12)
    (lo := (30089493 / 250000000)) (hi := (120357973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 886603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 886603) = 1/(886603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7648 : Bounds (-120357973 / 1000000000) (-30089493 / 250000000) (Real.log (886603 / 1000000)) := by
  have h := reflection_log_7648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7649_neg : (1294227 / 100000000) ≤ -Real.log (987141120391 / 1000000000000) ∧
    -Real.log (987141120391 / 1000000000000) ≤ (12942271 / 1000000000) := by
  have h := checkLog_sound (w := (12858879609 / 1987141120391)) (n := 12)
    (lo := (1294227 / 100000000)) (hi := (12942271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987141120391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987141120391) = 1/(987141120391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7649 : Bounds (-12942271 / 1000000000) (-1294227 / 100000000) (Real.log (987141120391 / 1000000000000)) := by
  have h := reflection_log_7649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7650_neg : (1283223 / 100000000) ≤ -Real.log (987249751111 / 1000000000000) ∧
    -Real.log (987249751111 / 1000000000000) ≤ (12832231 / 1000000000) := by
  have h := checkLog_sound (w := (12750248889 / 1987249751111)) (n := 12)
    (lo := (1283223 / 100000000)) (hi := (12832231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987249751111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987249751111) = 1/(987249751111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7650 : Bounds (-12832231 / 1000000000) (-1283223 / 100000000) (Real.log (987249751111 / 1000000000000)) := by
  have h := reflection_log_7650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7651_neg : (226801223 / 1000000000) ≤ -Real.log (100000000000 / 125458046203) ∧
    -Real.log (100000000000 / 125458046203) ≤ (28350153 / 125000000) := by
  have h := checkLog_sound (w := (25458046203 / 225458046203)) (n := 12)
    (lo := (226801223 / 1000000000)) (hi := (28350153 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125458046203 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125458046203 / 100000000000) = 1/(100000000000 / 125458046203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7651 : Bounds (226801223 / 1000000000) (28350153 / 125000000) (Real.log (125458046203 / 100000000000)) := by
  have h := reflection_log_7651_neg
  have he : Real.log (125458046203 / 100000000000) = -Real.log (100000000000 / 125458046203) := by
    rw [show ((125458046203 / 100000000000) : ℝ) = ((100000000000 / 125458046203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7652_neg : (9110947 / 40000000) ≤ -Real.log (25000000000 / 31395026861) ∧
    -Real.log (25000000000 / 31395026861) ≤ (56943419 / 250000000) := by
  have h := checkLog_sound (w := (6395026861 / 56395026861)) (n := 12)
    (lo := (9110947 / 40000000)) (hi := (56943419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31395026861 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31395026861 / 25000000000) = 1/(25000000000 / 31395026861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7652 : Bounds (9110947 / 40000000) (56943419 / 250000000) (Real.log (31395026861 / 25000000000)) := by
  have h := reflection_log_7652_neg
  have he : Real.log (31395026861 / 25000000000) = -Real.log (25000000000 / 31395026861) := by
    rw [show ((31395026861 / 25000000000) : ℝ) = ((25000000000 / 31395026861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7653_neg : (227863471 / 500000000) ≤ -Real.log (250000000000 / 394329896907) ∧
    -Real.log (250000000000 / 394329896907) ≤ (455726943 / 1000000000) := by
  have h := checkLog_sound (w := (144329896907 / 644329896907)) (n := 12)
    (lo := (227863471 / 500000000)) (hi := (455726943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394329896907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394329896907 / 250000000000) = 1/(250000000000 / 394329896907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7653 : Bounds (227863471 / 500000000) (455726943 / 1000000000) (Real.log (394329896907 / 250000000000)) := by
  have h := reflection_log_7653_neg
  have he : Real.log (394329896907 / 250000000000) = -Real.log (250000000000 / 394329896907) := by
    rw [show ((394329896907 / 250000000000) : ℝ) = ((250000000000 / 394329896907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7654_neg : (456779893 / 1000000000) ≤ -Real.log (500000000000 / 789490651193) ∧
    -Real.log (500000000000 / 789490651193) ≤ (228389947 / 500000000) := by
  have h := checkLog_sound (w := (289490651193 / 1289490651193)) (n := 12)
    (lo := (456779893 / 1000000000)) (hi := (228389947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789490651193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789490651193 / 500000000000) = 1/(500000000000 / 789490651193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7654 : Bounds (456779893 / 1000000000) (228389947 / 500000000) (Real.log (789490651193 / 500000000000)) := by
  have h := reflection_log_7654_neg
  have he : Real.log (789490651193 / 500000000000) = -Real.log (500000000000 / 789490651193) := by
    rw [show ((789490651193 / 500000000000) : ℝ) = ((500000000000 / 789490651193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7655_neg : (202940843 / 1000000000) ≤ -Real.log (40 / 49) ∧
    -Real.log (40 / 49) ≤ (50735211 / 250000000) := by
  have h := checkLog_sound (w := (9 / 89)) (n := 12)
    (lo := (202940843 / 1000000000)) (hi := (50735211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 40) = 1/(40 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7655 : Bounds (202940843 / 1000000000) (50735211 / 250000000) (Real.log (49 / 40)) := by
  have h := reflection_log_7655_neg
  have he : Real.log (49 / 40) = -Real.log (40 / 49) := by
    rw [show ((49 / 40) : ℝ) = ((40 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7656_neg : (254892249 / 1000000000) ≤ -Real.log (31 / 40) ∧
    -Real.log (31 / 40) ≤ (1019569 / 4000000) := by
  have h := checkLog_sound (w := (9 / 71)) (n := 12)
    (lo := (254892249 / 1000000000)) (hi := (1019569 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 31) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 31) = 1/(31 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7656 : Bounds (-1019569 / 4000000) (-254892249 / 1000000000) (Real.log (31 / 40)) := by
  have h := reflection_log_7656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7657_neg : (112487 / 500000000) ≤ -Real.log (40000 / 40009) ∧
    -Real.log (40000 / 40009) ≤ (8999 / 40000000) := by
  have h := checkLog_sound (w := (9 / 80009)) (n := 12)
    (lo := (112487 / 500000000)) (hi := (8999 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40009 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40009 / 40000) = 1/(40000 / 40009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7657 : Bounds (112487 / 500000000) (8999 / 40000000) (Real.log (40009 / 40000)) := by
  have h := reflection_log_7657_neg
  have he : Real.log (40009 / 40000) = -Real.log (40000 / 40009) := by
    rw [show ((40009 / 40000) : ℝ) = ((40000 / 40009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7658_neg : (9001 / 40000000) ≤ -Real.log (39991 / 40000) ∧
    -Real.log (39991 / 40000) ≤ (112513 / 500000000) := by
  have h := checkLog_sound (w := (9 / 79991)) (n := 12)
    (lo := (9001 / 40000000)) (hi := (112513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39991) = 1/(39991 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7658 : Bounds (-112513 / 500000000) (-9001 / 40000000) (Real.log (39991 / 40000)) := by
  have h := reflection_log_7658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7659_neg : (53607697 / 500000000) ≤ -Real.log (500000 / 556587) ∧
    -Real.log (500000 / 556587) ≤ (21443079 / 200000000) := by
  have h := checkLog_sound (w := (56587 / 1056587)) (n := 12)
    (lo := (53607697 / 500000000)) (hi := (21443079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556587 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(556587 / 500000) = 1/(500000 / 556587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7659 : Bounds (53607697 / 500000000) (21443079 / 200000000) (Real.log (556587 / 500000)) := by
  have h := reflection_log_7659_neg
  have he : Real.log (556587 / 500000) = -Real.log (500000 / 556587) := by
    rw [show ((556587 / 500000) : ℝ) = ((500000 / 556587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7660_neg : (60053241 / 500000000) ≤ -Real.log (443413 / 500000) ∧
    -Real.log (443413 / 500000) ≤ (120106483 / 1000000000) := by
  have h := checkLog_sound (w := (56587 / 943413)) (n := 12)
    (lo := (60053241 / 500000000)) (hi := (120106483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 443413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 443413) = 1/(443413 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7660 : Bounds (-120106483 / 1000000000) (-60053241 / 500000000) (Real.log (443413 / 500000)) := by
  have h := reflection_log_7660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7661_neg : (53823699 / 500000000) ≤ -Real.log (200000 / 222731) ∧
    -Real.log (200000 / 222731) ≤ (107647399 / 1000000000) := by
  have h := checkLog_sound (w := (22731 / 422731)) (n := 12)
    (lo := (53823699 / 500000000)) (hi := (107647399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222731 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222731 / 200000) = 1/(200000 / 222731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7661 : Bounds (53823699 / 500000000) (107647399 / 1000000000) (Real.log (222731 / 200000)) := by
  have h := reflection_log_7661_neg
  have he : Real.log (222731 / 200000) = -Real.log (200000 / 222731) := by
    rw [show ((222731 / 200000) : ℝ) = ((200000 / 222731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7662_neg : (120649013 / 1000000000) ≤ -Real.log (177269 / 200000) ∧
    -Real.log (177269 / 200000) ≤ (60324507 / 500000000) := by
  have h := checkLog_sound (w := (22731 / 377269)) (n := 12)
    (lo := (120649013 / 1000000000)) (hi := (60324507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 177269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 177269) = 1/(177269 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7662 : Bounds (-60324507 / 500000000) (-120649013 / 1000000000) (Real.log (177269 / 200000)) := by
  have h := reflection_log_7662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7663_neg : (6500807 / 500000000) ≤ -Real.log (39483301639 / 40000000000) ∧
    -Real.log (39483301639 / 40000000000) ≤ (2600323 / 200000000) := by
  have h := checkLog_sound (w := (516698361 / 79483301639)) (n := 12)
    (lo := (6500807 / 500000000)) (hi := (2600323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39483301639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39483301639) = 1/(39483301639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7663 : Bounds (-2600323 / 200000000) (-6500807 / 500000000) (Real.log (39483301639 / 40000000000)) := by
  have h := reflection_log_7663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7664_neg : (805693 / 62500000) ≤ -Real.log (246797911431 / 250000000000) ∧
    -Real.log (246797911431 / 250000000000) ≤ (12891089 / 1000000000) := by
  have h := checkLog_sound (w := (3202088569 / 496797911431)) (n := 12)
    (lo := (805693 / 62500000)) (hi := (12891089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246797911431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246797911431) = 1/(246797911431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7664 : Bounds (-12891089 / 1000000000) (-805693 / 62500000) (Real.log (246797911431 / 250000000000)) := by
  have h := reflection_log_7664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7665_neg : (227321877 / 1000000000) ≤ -Real.log (3125000000 / 3922605731) ∧
    -Real.log (3125000000 / 3922605731) ≤ (113660939 / 500000000) := by
  have h := checkLog_sound (w := (797605731 / 7047605731)) (n := 12)
    (lo := (227321877 / 1000000000)) (hi := (113660939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3922605731 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3922605731 / 3125000000) = 1/(3125000000 / 3922605731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7665 : Bounds (227321877 / 1000000000) (113660939 / 500000000) (Real.log (3922605731 / 3125000000)) := by
  have h := reflection_log_7665_neg
  have he : Real.log (3922605731 / 3125000000) = -Real.log (3125000000 / 3922605731) := by
    rw [show ((3922605731 / 3125000000) : ℝ) = ((3125000000 / 3922605731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7666_neg : (57074103 / 250000000) ≤ -Real.log (25000000000 / 31411442497) ∧
    -Real.log (25000000000 / 31411442497) ≤ (228296413 / 1000000000) := by
  have h := checkLog_sound (w := (6411442497 / 56411442497)) (n := 12)
    (lo := (57074103 / 250000000)) (hi := (228296413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31411442497 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31411442497 / 25000000000) = 1/(25000000000 / 31411442497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7666 : Bounds (57074103 / 250000000) (228296413 / 1000000000) (Real.log (31411442497 / 25000000000)) := by
  have h := reflection_log_7666_neg
  have he : Real.log (31411442497 / 25000000000) = -Real.log (25000000000 / 31411442497) := by
    rw [show ((31411442497 / 25000000000) : ℝ) = ((25000000000 / 31411442497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7667_neg : (456779893 / 1000000000) ≤ -Real.log (62500000000 / 98686331399) ∧
    -Real.log (62500000000 / 98686331399) ≤ (228389947 / 500000000) := by
  have h := checkLog_sound (w := (36186331399 / 161186331399)) (n := 12)
    (lo := (456779893 / 1000000000)) (hi := (228389947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98686331399 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98686331399 / 62500000000) = 1/(62500000000 / 98686331399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7667 : Bounds (456779893 / 1000000000) (228389947 / 500000000) (Real.log (98686331399 / 62500000000)) := by
  have h := reflection_log_7667_neg
  have he : Real.log (98686331399 / 62500000000) = -Real.log (62500000000 / 98686331399) := by
    rw [show ((98686331399 / 62500000000) : ℝ) = ((62500000000 / 98686331399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7668_neg : (457833093 / 1000000000) ≤ -Real.log (250000000000 / 395161290323) ∧
    -Real.log (250000000000 / 395161290323) ≤ (228916547 / 500000000) := by
  have h := checkLog_sound (w := (145161290323 / 645161290323)) (n := 12)
    (lo := (457833093 / 1000000000)) (hi := (228916547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395161290323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395161290323 / 250000000000) = 1/(250000000000 / 395161290323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7668 : Bounds (457833093 / 1000000000) (228916547 / 500000000) (Real.log (395161290323 / 250000000000)) := by
  have h := reflection_log_7668_neg
  have he : Real.log (395161290323 / 250000000000) = -Real.log (250000000000 / 395161290323) := by
    rw [show ((395161290323 / 250000000000) : ℝ) = ((250000000000 / 395161290323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7669_neg : (203348923 / 1000000000) ≤ -Real.log (2000 / 2451) ∧
    -Real.log (2000 / 2451) ≤ (50837231 / 250000000) := by
  have h := checkLog_sound (w := (451 / 4451)) (n := 12)
    (lo := (203348923 / 1000000000)) (hi := (50837231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2451 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2451 / 2000) = 1/(2000 / 2451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7669 : Bounds (203348923 / 1000000000) (50837231 / 250000000) (Real.log (2451 / 2000)) := by
  have h := reflection_log_7669_neg
  have he : Real.log (2451 / 2000) = -Real.log (2000 / 2451) := by
    rw [show ((2451 / 2000) : ℝ) = ((2000 / 2451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7670_neg : (255537619 / 1000000000) ≤ -Real.log (1549 / 2000) ∧
    -Real.log (1549 / 2000) ≤ (12776881 / 50000000) := by
  have h := checkLog_sound (w := (451 / 3549)) (n := 12)
    (lo := (255537619 / 1000000000)) (hi := (12776881 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1549) = 1/(1549 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7670 : Bounds (-12776881 / 50000000) (-255537619 / 1000000000) (Real.log (1549 / 2000)) := by
  have h := reflection_log_7670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7671_neg : (112737 / 500000000) ≤ -Real.log (2000000 / 2000451) ∧
    -Real.log (2000000 / 2000451) ≤ (9019 / 40000000) := by
  have h := checkLog_sound (w := (451 / 4000451)) (n := 12)
    (lo := (112737 / 500000000)) (hi := (9019 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000451 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000451 / 2000000) = 1/(2000000 / 2000451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7671 : Bounds (112737 / 500000000) (9019 / 40000000) (Real.log (2000451 / 2000000)) := by
  have h := reflection_log_7671_neg
  have he : Real.log (2000451 / 2000000) = -Real.log (2000000 / 2000451) := by
    rw [show ((2000451 / 2000000) : ℝ) = ((2000000 / 2000451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7672_neg : (9021 / 40000000) ≤ -Real.log (1999549 / 2000000) ∧
    -Real.log (1999549 / 2000000) ≤ (112763 / 500000000) := by
  have h := checkLog_sound (w := (451 / 3999549)) (n := 12)
    (lo := (9021 / 40000000)) (hi := (112763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999549) = 1/(1999549 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7672 : Bounds (-112763 / 500000000) (-9021 / 40000000) (Real.log (1999549 / 2000000)) := by
  have h := reflection_log_7672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7673_neg : (107446239 / 1000000000) ≤ -Real.log (1000000 / 1113431) ∧
    -Real.log (1000000 / 1113431) ≤ (671539 / 6250000) := by
  have h := checkLog_sound (w := (113431 / 2113431)) (n := 12)
    (lo := (107446239 / 1000000000)) (hi := (671539 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1113431 / 1000000) = 1/(1000000 / 1113431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7673 : Bounds (107446239 / 1000000000) (671539 / 6250000) (Real.log (1113431 / 1000000)) := by
  have h := reflection_log_7673_neg
  have he : Real.log (1113431 / 1000000) = -Real.log (1000000 / 1113431) := by
    rw [show ((1113431 / 1000000) : ℝ) = ((1000000 / 1113431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7674_neg : (60198161 / 500000000) ≤ -Real.log (886569 / 1000000) ∧
    -Real.log (886569 / 1000000) ≤ (120396323 / 1000000000) := by
  have h := checkLog_sound (w := (113431 / 1886569)) (n := 12)
    (lo := (60198161 / 500000000)) (hi := (120396323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 886569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 886569) = 1/(886569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7674 : Bounds (-120396323 / 1000000000) (-60198161 / 500000000) (Real.log (886569 / 1000000)) := by
  have h := reflection_log_7674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7675_neg : (107878143 / 1000000000) ≤ -Real.log (125000 / 139239) ∧
    -Real.log (125000 / 139239) ≤ (421399 / 3906250) := by
  have h := checkLog_sound (w := (14239 / 264239)) (n := 12)
    (lo := (107878143 / 1000000000)) (hi := (421399 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139239 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139239 / 125000) = 1/(125000 / 139239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7675 : Bounds (107878143 / 1000000000) (421399 / 3906250) (Real.log (139239 / 125000)) := by
  have h := reflection_log_7675_neg
  have he : Real.log (139239 / 125000) = -Real.log (125000 / 139239) := by
    rw [show ((139239 / 125000) : ℝ) = ((125000 / 139239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7676_neg : (12093901 / 100000000) ≤ -Real.log (110761 / 125000) ∧
    -Real.log (110761 / 125000) ≤ (120939011 / 1000000000) := by
  have h := checkLog_sound (w := (14239 / 235761)) (n := 12)
    (lo := (12093901 / 100000000)) (hi := (120939011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110761) = 1/(110761 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7676 : Bounds (-120939011 / 1000000000) (-12093901 / 100000000) (Real.log (110761 / 125000)) := by
  have h := reflection_log_7676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7677_neg : (6530433 / 500000000) ≤ -Real.log (15422250879 / 15625000000) ∧
    -Real.log (15422250879 / 15625000000) ≤ (13060867 / 1000000000) := by
  have h := checkLog_sound (w := (202749121 / 31047250879)) (n := 12)
    (lo := (6530433 / 500000000)) (hi := (13060867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15422250879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15422250879) = 1/(15422250879 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7677 : Bounds (-13060867 / 1000000000) (-6530433 / 500000000) (Real.log (15422250879 / 15625000000)) := by
  have h := reflection_log_7677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7678_neg : (12950083 / 1000000000) ≤ -Real.log (987133408239 / 1000000000000) ∧
    -Real.log (987133408239 / 1000000000000) ≤ (3237521 / 250000000) := by
  have h := checkLog_sound (w := (12866591761 / 1987133408239)) (n := 12)
    (lo := (12950083 / 1000000000)) (hi := (3237521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987133408239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987133408239) = 1/(987133408239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7678 : Bounds (-3237521 / 250000000) (-12950083 / 1000000000) (Real.log (987133408239 / 1000000000000)) := by
  have h := reflection_log_7678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7679_neg : (227842561 / 1000000000) ≤ -Real.log (31250000000 / 39246487019) ∧
    -Real.log (31250000000 / 39246487019) ≤ (113921281 / 500000000) := by
  have h := checkLog_sound (w := (7996487019 / 70496487019)) (n := 12)
    (lo := (227842561 / 1000000000)) (hi := (113921281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39246487019 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39246487019 / 31250000000) = 1/(31250000000 / 39246487019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7679 : Bounds (227842561 / 1000000000) (113921281 / 500000000) (Real.log (39246487019 / 31250000000)) := by
  have h := reflection_log_7679_neg
  have he : Real.log (39246487019 / 31250000000) = -Real.log (31250000000 / 39246487019) := by
    rw [show ((39246487019 / 31250000000) : ℝ) = ((31250000000 / 39246487019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


