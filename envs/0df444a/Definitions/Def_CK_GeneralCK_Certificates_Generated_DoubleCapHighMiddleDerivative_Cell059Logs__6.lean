-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell059Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell059Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:10:55.740226+00:00
-- url     : https://prove2.me/theorems/668f972e-d204-4fcb-a3df-077ae7cb7454
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell059Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell060…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell059Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell060Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell061Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell062Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell063Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell064Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell059Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell060Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell061Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell062Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell063Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell064Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell059Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell060Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell061Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell062Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell063Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell064Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell059Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell060Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell061Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell062Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell063Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell064Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell059Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell059
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (125440153 / 500000000) ≤ -Real.log (256 / 329) ∧
    -Real.log (256 / 329) ≤ (250880307 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 585)) (n := 12)
    (lo := (125440153 / 500000000)) (hi := (250880307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329 / 256) = 1/(256 / 329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (125440153 / 500000000) (250880307 / 1000000000) (Real.log (329 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (329 / 256) = -Real.log (256 / 329) := by
    rw [show ((329 / 256) : ℝ) = ((256 / 329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (335691291 / 1000000000) ≤ -Real.log (183 / 256) ∧
    -Real.log (183 / 256) ≤ (83922823 / 250000000) := by
  have h := checkLog_sound (w := (73 / 439)) (n := 12)
    (lo := (335691291 / 1000000000)) (hi := (83922823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 183) = 1/(183 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83922823 / 250000000) (-335691291 / 1000000000) (Real.log (183 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10016971 / 40000000) ≤ -Real.log (5120 / 6577) ∧
    -Real.log (5120 / 6577) ≤ (62606069 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 11697)) (n := 12)
    (lo := (10016971 / 40000000)) (hi := (62606069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6577 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6577 / 5120) = 1/(5120 / 6577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10016971 / 40000000) (62606069 / 250000000) (Real.log (6577 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6577 / 5120) = -Real.log (5120 / 6577) := by
    rw [show ((6577 / 5120) : ℝ) = ((5120 / 6577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (66974391 / 200000000) ≤ -Real.log (3663 / 5120) ∧
    -Real.log (3663 / 5120) ≤ (83717989 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 8783)) (n := 12)
    (lo := (66974391 / 200000000)) (hi := (83717989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3663) = 1/(3663 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83717989 / 250000000) (-66974391 / 200000000) (Real.log (3663 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (91961803 / 500000000) ≤ -Real.log (250000 / 300481) ∧
    -Real.log (250000 / 300481) ≤ (183923607 / 1000000000) := by
  have h := checkLog_sound (w := (50481 / 550481)) (n := 12)
    (lo := (91961803 / 500000000)) (hi := (183923607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300481 / 250000) = 1/(250000 / 300481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (91961803 / 500000000) (183923607 / 1000000000) (Real.log (300481 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (300481 / 250000) = -Real.log (250000 / 300481) := by
    rw [show ((300481 / 250000) : ℝ) = ((250000 / 300481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (225551447 / 1000000000) ≤ -Real.log (199519 / 250000) ∧
    -Real.log (199519 / 250000) ≤ (28193931 / 125000000) := by
  have h := checkLog_sound (w := (50481 / 449519)) (n := 12)
    (lo := (225551447 / 1000000000)) (hi := (28193931 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 199519) = 1/(199519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-28193931 / 125000000) (-225551447 / 1000000000) (Real.log (199519 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23034123 / 125000000) ≤ -Real.log (125000 / 150293) ∧
    -Real.log (125000 / 150293) ≤ (36854597 / 200000000) := by
  have h := checkLog_sound (w := (25293 / 275293)) (n := 12)
    (lo := (23034123 / 125000000)) (hi := (36854597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150293 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150293 / 125000) = 1/(125000 / 150293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23034123 / 125000000) (36854597 / 200000000) (Real.log (150293 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (150293 / 125000) = -Real.log (125000 / 150293) := by
    rw [show ((150293 / 125000) : ℝ) = ((125000 / 150293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (56519463 / 250000000) ≤ -Real.log (99707 / 125000) ∧
    -Real.log (99707 / 125000) ≤ (226077853 / 1000000000) := by
  have h := checkLog_sound (w := (25293 / 224707)) (n := 12)
    (lo := (56519463 / 250000000)) (hi := (226077853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 99707) = 1/(99707 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-226077853 / 1000000000) (-56519463 / 250000000) (Real.log (99707 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (134891841 / 1000000000) ≤ -Real.log (1000000 / 1144413) ∧
    -Real.log (1000000 / 1144413) ≤ (67445921 / 500000000) := by
  have h := checkLog_sound (w := (144413 / 2144413)) (n := 12)
    (lo := (134891841 / 1000000000)) (hi := (67445921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144413 / 1000000) = 1/(1000000 / 1144413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (134891841 / 1000000000) (67445921 / 500000000) (Real.log (1144413 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1144413 / 1000000) = -Real.log (1000000 / 1144413) := by
    rw [show ((1144413 / 1000000) : ℝ) = ((1000000 / 1144413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31193499 / 200000000) ≤ -Real.log (855587 / 1000000) ∧
    -Real.log (855587 / 1000000) ≤ (19495937 / 125000000) := by
  have h := checkLog_sound (w := (144413 / 1855587)) (n := 12)
    (lo := (31193499 / 200000000)) (hi := (19495937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855587) = 1/(855587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19495937 / 125000000) (-31193499 / 200000000) (Real.log (855587 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135160939 / 1000000000) ≤ -Real.log (1000000 / 1144721) ∧
    -Real.log (1000000 / 1144721) ≤ (6758047 / 50000000) := by
  have h := checkLog_sound (w := (144721 / 2144721)) (n := 12)
    (lo := (135160939 / 1000000000)) (hi := (6758047 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144721 / 1000000) = 1/(1000000 / 1144721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135160939 / 1000000000) (6758047 / 50000000) (Real.log (1144721 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1144721 / 1000000) = -Real.log (1000000 / 1144721) := by
    rw [show ((1144721 / 1000000) : ℝ) = ((1000000 / 1144721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (156327547 / 1000000000) ≤ -Real.log (855279 / 1000000) ∧
    -Real.log (855279 / 1000000) ≤ (39081887 / 250000000) := by
  have h := checkLog_sound (w := (144721 / 1855279)) (n := 12)
    (lo := (156327547 / 1000000000)) (hi := (39081887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855279) = 1/(855279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-39081887 / 250000000) (-156327547 / 1000000000) (Real.log (855279 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58529623 / 100000000) ≤ -Real.log (500000000000 / 897761397761) ∧
    -Real.log (500000000000 / 897761397761) ≤ (585296231 / 1000000000) := by
  have h := checkLog_sound (w := (397761397761 / 1397761397761)) (n := 12)
    (lo := (58529623 / 100000000)) (hi := (585296231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897761397761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897761397761 / 500000000000) = 1/(500000000000 / 897761397761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58529623 / 100000000) (585296231 / 1000000000) (Real.log (897761397761 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (897761397761 / 500000000000) = -Real.log (500000000000 / 897761397761) := by
    rw [show ((897761397761 / 500000000000) : ℝ) = ((500000000000 / 897761397761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (586571597 / 1000000000) ≤ -Real.log (250000000000 / 449453551913) ∧
    -Real.log (250000000000 / 449453551913) ≤ (293285799 / 500000000) := by
  have h := checkLog_sound (w := (199453551913 / 699453551913)) (n := 12)
    (lo := (586571597 / 1000000000)) (hi := (293285799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449453551913 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449453551913 / 250000000000) = 1/(250000000000 / 449453551913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (586571597 / 1000000000) (293285799 / 500000000) (Real.log (449453551913 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (449453551913 / 250000000000) = -Real.log (250000000000 / 449453551913) := by
    rw [show ((449453551913 / 250000000000) : ℝ) = ((250000000000 / 449453551913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (204737527 / 500000000) ≤ -Real.log (500000000000 / 753013497461) ∧
    -Real.log (500000000000 / 753013497461) ≤ (81895011 / 200000000) := by
  have h := checkLog_sound (w := (253013497461 / 1253013497461)) (n := 12)
    (lo := (204737527 / 500000000)) (hi := (81895011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753013497461 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753013497461 / 500000000000) = 1/(500000000000 / 753013497461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204737527 / 500000000) (81895011 / 200000000) (Real.log (753013497461 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (753013497461 / 500000000000) = -Real.log (500000000000 / 753013497461) := by
    rw [show ((753013497461 / 500000000000) : ℝ) = ((500000000000 / 753013497461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (410350837 / 1000000000) ≤ -Real.log (25000000000 / 37683663133) ∧
    -Real.log (25000000000 / 37683663133) ≤ (205175419 / 500000000) := by
  have h := checkLog_sound (w := (12683663133 / 62683663133)) (n := 12)
    (lo := (410350837 / 1000000000)) (hi := (205175419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37683663133 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37683663133 / 25000000000) = 1/(25000000000 / 37683663133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (410350837 / 1000000000) (205175419 / 500000000) (Real.log (37683663133 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (37683663133 / 25000000000) = -Real.log (25000000000 / 37683663133) := by
    rw [show ((37683663133 / 25000000000) : ℝ) = ((25000000000 / 37683663133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (290859337 / 1000000000) ≤ -Real.log (500000000000 / 668788212069) ∧
    -Real.log (500000000000 / 668788212069) ≤ (145429669 / 500000000) := by
  have h := checkLog_sound (w := (168788212069 / 1168788212069)) (n := 12)
    (lo := (290859337 / 1000000000)) (hi := (145429669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668788212069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668788212069 / 500000000000) = 1/(500000000000 / 668788212069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (290859337 / 1000000000) (145429669 / 500000000) (Real.log (668788212069 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (668788212069 / 500000000000) = -Real.log (500000000000 / 668788212069) := by
    rw [show ((668788212069 / 500000000000) : ℝ) = ((500000000000 / 668788212069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (145744243 / 500000000) ≤ -Real.log (500000000000 / 669209111881) ∧
    -Real.log (500000000000 / 669209111881) ≤ (291488487 / 1000000000) := by
  have h := checkLog_sound (w := (169209111881 / 1169209111881)) (n := 12)
    (lo := (145744243 / 500000000)) (hi := (291488487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669209111881 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669209111881 / 500000000000) = 1/(500000000000 / 669209111881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (145744243 / 500000000) (291488487 / 1000000000) (Real.log (669209111881 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (669209111881 / 500000000000) = -Real.log (500000000000 / 669209111881) := by
    rw [show ((669209111881 / 500000000000) : ℝ) = ((500000000000 / 669209111881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1322913 / 62500000) ≤ -Real.log (979055832159 / 1000000000000) ∧
    -Real.log (979055832159 / 1000000000000) ≤ (21166609 / 1000000000) := by
  have h := checkLog_sound (w := (20944167841 / 1979055832159)) (n := 12)
    (lo := (1322913 / 62500000)) (hi := (21166609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979055832159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979055832159) = 1/(979055832159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21166609 / 1000000000) (-1322913 / 62500000) (Real.log (979055832159 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10537827 / 500000000) ≤ -Real.log (979144885431 / 1000000000000) ∧
    -Real.log (979144885431 / 1000000000000) ≤ (4215131 / 200000000) := by
  have h := checkLog_sound (w := (20855114569 / 1979144885431)) (n := 12)
    (lo := (10537827 / 500000000)) (hi := (4215131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979144885431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979144885431) = 1/(979144885431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4215131 / 200000000) (-10537827 / 500000000) (Real.log (979144885431 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell059

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell060Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell060
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (251336129 / 1000000000) ≤ -Real.log (5120 / 6583) ∧
    -Real.log (5120 / 6583) ≤ (25133613 / 100000000) := by
  have h := checkLog_sound (w := (1463 / 11703)) (n := 12)
    (lo := (251336129 / 1000000000)) (hi := (25133613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6583 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6583 / 5120) = 1/(5120 / 6583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (251336129 / 1000000000) (25133613 / 100000000) (Real.log (6583 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6583 / 5120) = -Real.log (5120 / 6583) := by
    rw [show ((6583 / 5120) : ℝ) = ((5120 / 6583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (336511299 / 1000000000) ≤ -Real.log (3657 / 5120) ∧
    -Real.log (3657 / 5120) ≤ (3365113 / 10000000) := by
  have h := checkLog_sound (w := (1463 / 8777)) (n := 12)
    (lo := (336511299 / 1000000000)) (hi := (3365113 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3657) = 1/(3657 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3365113 / 10000000) (-336511299 / 1000000000) (Real.log (3657 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (125440153 / 500000000) ≤ -Real.log (256 / 329) ∧
    -Real.log (256 / 329) ≤ (250880307 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 585)) (n := 12)
    (lo := (125440153 / 500000000)) (hi := (250880307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329 / 256) = 1/(256 / 329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (125440153 / 500000000) (250880307 / 1000000000) (Real.log (329 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (329 / 256) = -Real.log (256 / 329) := by
    rw [show ((329 / 256) : ℝ) = ((256 / 329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (335691291 / 1000000000) ≤ -Real.log (183 / 256) ∧
    -Real.log (183 / 256) ≤ (83922823 / 250000000) := by
  have h := checkLog_sound (w := (73 / 439)) (n := 12)
    (lo := (335691291 / 1000000000)) (hi := (83922823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 183) = 1/(183 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83922823 / 250000000) (-335691291 / 1000000000) (Real.log (183 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184272153 / 1000000000) ≤ -Real.log (1000000 / 1202343) ∧
    -Real.log (1000000 / 1202343) ≤ (92136077 / 500000000) := by
  have h := checkLog_sound (w := (202343 / 2202343)) (n := 12)
    (lo := (184272153 / 1000000000)) (hi := (92136077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202343 / 1000000) = 1/(1000000 / 1202343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184272153 / 1000000000) (92136077 / 500000000) (Real.log (1202343 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1202343 / 1000000) = -Real.log (1000000 / 1202343) := by
    rw [show ((1202343 / 1000000) : ℝ) = ((1000000 / 1202343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (113038299 / 500000000) ≤ -Real.log (797657 / 1000000) ∧
    -Real.log (797657 / 1000000) ≤ (226076599 / 1000000000) := by
  have h := checkLog_sound (w := (202343 / 1797657)) (n := 12)
    (lo := (113038299 / 500000000)) (hi := (226076599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797657) = 1/(797657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-226076599 / 1000000000) (-113038299 / 500000000) (Real.log (797657 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (92310289 / 500000000) ≤ -Real.log (500000 / 601381) ∧
    -Real.log (500000 / 601381) ≤ (184620579 / 1000000000) := by
  have h := checkLog_sound (w := (101381 / 1101381)) (n := 12)
    (lo := (92310289 / 500000000)) (hi := (184620579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601381 / 500000) = 1/(500000 / 601381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (92310289 / 500000000) (184620579 / 1000000000) (Real.log (601381 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (601381 / 500000) = -Real.log (500000 / 601381) := by
    rw [show ((601381 / 500000) : ℝ) = ((500000 / 601381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28325253 / 125000000) ≤ -Real.log (398619 / 500000) ∧
    -Real.log (398619 / 500000) ≤ (9064081 / 40000000) := by
  have h := checkLog_sound (w := (101381 / 898619)) (n := 12)
    (lo := (28325253 / 125000000)) (hi := (9064081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 398619) = 1/(398619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9064081 / 40000000) (-28325253 / 125000000) (Real.log (398619 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27032013 / 200000000) ≤ -Real.log (12500 / 14309) ∧
    -Real.log (12500 / 14309) ≤ (67580033 / 500000000) := by
  have h := checkLog_sound (w := (1809 / 26809)) (n := 12)
    (lo := (27032013 / 200000000)) (hi := (67580033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14309 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14309 / 12500) = 1/(12500 / 14309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27032013 / 200000000) (67580033 / 500000000) (Real.log (14309 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (14309 / 12500) = -Real.log (12500 / 14309) := by
    rw [show ((14309 / 12500) : ℝ) = ((12500 / 14309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (78163189 / 500000000) ≤ -Real.log (10691 / 12500) ∧
    -Real.log (10691 / 12500) ≤ (156326379 / 1000000000) := by
  have h := checkLog_sound (w := (1809 / 23191)) (n := 12)
    (lo := (78163189 / 500000000)) (hi := (156326379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10691) = 1/(10691 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-156326379 / 1000000000) (-78163189 / 500000000) (Real.log (10691 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135428217 / 1000000000) ≤ -Real.log (1000000 / 1145027) ∧
    -Real.log (1000000 / 1145027) ≤ (67714109 / 500000000) := by
  have h := checkLog_sound (w := (145027 / 2145027)) (n := 12)
    (lo := (135428217 / 1000000000)) (hi := (67714109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145027 / 1000000) = 1/(1000000 / 1145027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135428217 / 1000000000) (67714109 / 500000000) (Real.log (1145027 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1145027 / 1000000) = -Real.log (1000000 / 1145027) := by
    rw [show ((1145027 / 1000000) : ℝ) = ((1000000 / 1145027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (156685389 / 1000000000) ≤ -Real.log (854973 / 1000000) ∧
    -Real.log (854973 / 1000000) ≤ (15668539 / 100000000) := by
  have h := checkLog_sound (w := (145027 / 1854973)) (n := 12)
    (lo := (156685389 / 1000000000)) (hi := (15668539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854973) = 1/(854973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15668539 / 100000000) (-156685389 / 1000000000) (Real.log (854973 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (586571597 / 1000000000) ≤ -Real.log (20000000000 / 35956284153) ∧
    -Real.log (20000000000 / 35956284153) ≤ (293285799 / 500000000) := by
  have h := checkLog_sound (w := (15956284153 / 55956284153)) (n := 12)
    (lo := (586571597 / 1000000000)) (hi := (293285799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35956284153 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35956284153 / 20000000000) = 1/(20000000000 / 35956284153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (586571597 / 1000000000) (293285799 / 500000000) (Real.log (35956284153 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (35956284153 / 20000000000) = -Real.log (20000000000 / 35956284153) := by
    rw [show ((35956284153 / 20000000000) : ℝ) = ((20000000000 / 35956284153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (587847429 / 1000000000) ≤ -Real.log (500000000000 / 900054689637) ∧
    -Real.log (500000000000 / 900054689637) ≤ (58784743 / 100000000) := by
  have h := checkLog_sound (w := (400054689637 / 1400054689637)) (n := 12)
    (lo := (587847429 / 1000000000)) (hi := (58784743 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900054689637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900054689637 / 500000000000) = 1/(500000000000 / 900054689637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (587847429 / 1000000000) (58784743 / 100000000) (Real.log (900054689637 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (900054689637 / 500000000000) = -Real.log (500000000000 / 900054689637) := by
    rw [show ((900054689637 / 500000000000) : ℝ) = ((500000000000 / 900054689637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (410348751 / 1000000000) ≤ -Real.log (125000000000 / 188417922741) ∧
    -Real.log (125000000000 / 188417922741) ≤ (25646797 / 62500000) := by
  have h := checkLog_sound (w := (63417922741 / 313417922741)) (n := 12)
    (lo := (410348751 / 1000000000)) (hi := (25646797 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188417922741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188417922741 / 125000000000) = 1/(125000000000 / 188417922741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (410348751 / 1000000000) (25646797 / 62500000) (Real.log (188417922741 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (188417922741 / 125000000000) = -Real.log (125000000000 / 188417922741) := by
    rw [show ((188417922741 / 125000000000) : ℝ) = ((125000000000 / 188417922741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (411222603 / 1000000000) ≤ -Real.log (100000000000 / 150866115263) ∧
    -Real.log (100000000000 / 150866115263) ≤ (102805651 / 250000000) := by
  have h := checkLog_sound (w := (50866115263 / 250866115263)) (n := 12)
    (lo := (411222603 / 1000000000)) (hi := (102805651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150866115263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150866115263 / 100000000000) = 1/(100000000000 / 150866115263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (411222603 / 1000000000) (102805651 / 250000000) (Real.log (150866115263 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (150866115263 / 100000000000) = -Real.log (100000000000 / 150866115263) := by
    rw [show ((150866115263 / 100000000000) : ℝ) = ((100000000000 / 150866115263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (291486443 / 1000000000) ≤ -Real.log (7812500000 / 10456371013) ∧
    -Real.log (7812500000 / 10456371013) ≤ (72871611 / 250000000) := by
  have h := checkLog_sound (w := (2643871013 / 18268871013)) (n := 12)
    (lo := (291486443 / 1000000000)) (hi := (72871611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10456371013 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10456371013 / 7812500000) = 1/(7812500000 / 10456371013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (291486443 / 1000000000) (72871611 / 250000000) (Real.log (10456371013 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10456371013 / 7812500000) = -Real.log (7812500000 / 10456371013) := by
    rw [show ((10456371013 / 7812500000) : ℝ) = ((7812500000 / 10456371013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (292113607 / 1000000000) ≤ -Real.log (500000000000 / 669627578883) ∧
    -Real.log (500000000000 / 669627578883) ≤ (36514201 / 125000000) := by
  have h := checkLog_sound (w := (169627578883 / 1169627578883)) (n := 12)
    (lo := (292113607 / 1000000000)) (hi := (36514201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669627578883 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669627578883 / 500000000000) = 1/(500000000000 / 669627578883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (292113607 / 1000000000) (36514201 / 125000000) (Real.log (669627578883 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (669627578883 / 500000000000) = -Real.log (500000000000 / 669627578883) := by
    rw [show ((669627578883 / 500000000000) : ℝ) = ((500000000000 / 669627578883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21257171 / 1000000000) ≤ -Real.log (978967169271 / 1000000000000) ∧
    -Real.log (978967169271 / 1000000000000) ≤ (5314293 / 250000000) := by
  have h := checkLog_sound (w := (21032830729 / 1978967169271)) (n := 12)
    (lo := (21257171 / 1000000000)) (hi := (5314293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978967169271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978967169271) = 1/(978967169271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5314293 / 250000000) (-21257171 / 1000000000) (Real.log (978967169271 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2645789 / 125000000) ≤ -Real.log (152977519 / 156250000) ∧
    -Real.log (152977519 / 156250000) ≤ (21166313 / 1000000000) := by
  have h := checkLog_sound (w := (3272481 / 309227519)) (n := 12)
    (lo := (2645789 / 125000000)) (hi := (21166313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 152977519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 152977519) = 1/(152977519 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21166313 / 1000000000) (-2645789 / 125000000) (Real.log (152977519 / 156250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell060

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell061Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell061
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (1967123 / 7812500) ≤ -Real.log (2560 / 3293) ∧
    -Real.log (2560 / 3293) ≤ (50358349 / 200000000) := by
  have h := checkLog_sound (w := (733 / 5853)) (n := 12)
    (lo := (1967123 / 7812500)) (hi := (50358349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3293 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3293 / 2560) = 1/(2560 / 3293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1967123 / 7812500) (50358349 / 200000000) (Real.log (3293 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3293 / 2560) = -Real.log (2560 / 3293) := by
    rw [show ((3293 / 2560) : ℝ) = ((2560 / 3293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (337331981 / 1000000000) ≤ -Real.log (1827 / 2560) ∧
    -Real.log (1827 / 2560) ≤ (168665991 / 500000000) := by
  have h := checkLog_sound (w := (733 / 4387)) (n := 12)
    (lo := (337331981 / 1000000000)) (hi := (168665991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1827) = 1/(1827 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-168665991 / 500000000) (-337331981 / 1000000000) (Real.log (1827 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (251336129 / 1000000000) ≤ -Real.log (5120 / 6583) ∧
    -Real.log (5120 / 6583) ≤ (25133613 / 100000000) := by
  have h := checkLog_sound (w := (1463 / 11703)) (n := 12)
    (lo := (251336129 / 1000000000)) (hi := (25133613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6583 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6583 / 5120) = 1/(5120 / 6583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (251336129 / 1000000000) (25133613 / 100000000) (Real.log (6583 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6583 / 5120) = -Real.log (5120 / 6583) := by
    rw [show ((6583 / 5120) : ℝ) = ((5120 / 6583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (336511299 / 1000000000) ≤ -Real.log (3657 / 5120) ∧
    -Real.log (3657 / 5120) ≤ (3365113 / 10000000) := by
  have h := checkLog_sound (w := (1463 / 8777)) (n := 12)
    (lo := (336511299 / 1000000000)) (hi := (3365113 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3657) = 1/(3657 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3365113 / 10000000) (-336511299 / 1000000000) (Real.log (3657 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184619747 / 1000000000) ≤ -Real.log (1000000 / 1202761) ∧
    -Real.log (1000000 / 1202761) ≤ (46154937 / 250000000) := by
  have h := checkLog_sound (w := (202761 / 2202761)) (n := 12)
    (lo := (184619747 / 1000000000)) (hi := (46154937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202761 / 1000000) = 1/(1000000 / 1202761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184619747 / 1000000000) (46154937 / 250000000) (Real.log (1202761 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1202761 / 1000000) = -Real.log (1000000 / 1202761) := by
    rw [show ((1202761 / 1000000) : ℝ) = ((1000000 / 1202761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (22660077 / 100000000) ≤ -Real.log (797239 / 1000000) ∧
    -Real.log (797239 / 1000000) ≤ (226600771 / 1000000000) := by
  have h := checkLog_sound (w := (202761 / 1797239)) (n := 12)
    (lo := (22660077 / 100000000)) (hi := (226600771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797239) = 1/(797239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-226600771 / 1000000000) (-22660077 / 100000000) (Real.log (797239 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (92484441 / 500000000) ≤ -Real.log (1000000 / 1203181) ∧
    -Real.log (1000000 / 1203181) ≤ (184968883 / 1000000000) := by
  have h := checkLog_sound (w := (203181 / 2203181)) (n := 12)
    (lo := (92484441 / 500000000)) (hi := (184968883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203181 / 1000000) = 1/(1000000 / 1203181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (92484441 / 500000000) (184968883 / 1000000000) (Real.log (1203181 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1203181 / 1000000) = -Real.log (1000000 / 1203181) := by
    rw [show ((1203181 / 1000000) : ℝ) = ((1000000 / 1203181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (227127727 / 1000000000) ≤ -Real.log (796819 / 1000000) ∧
    -Real.log (796819 / 1000000) ≤ (14195483 / 62500000) := by
  have h := checkLog_sound (w := (203181 / 1796819)) (n := 12)
    (lo := (227127727 / 1000000000)) (hi := (14195483 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796819) = 1/(796819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-14195483 / 62500000) (-227127727 / 1000000000) (Real.log (796819 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8464209 / 62500000) ≤ -Real.log (500000 / 572513) ∧
    -Real.log (500000 / 572513) ≤ (27085469 / 200000000) := by
  have h := checkLog_sound (w := (72513 / 1072513)) (n := 12)
    (lo := (8464209 / 62500000)) (hi := (27085469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572513 / 500000) = 1/(500000 / 572513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8464209 / 62500000) (27085469 / 200000000) (Real.log (572513 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (572513 / 500000) = -Real.log (500000 / 572513) := by
    rw [show ((572513 / 500000) : ℝ) = ((500000 / 572513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (156684219 / 1000000000) ≤ -Real.log (427487 / 500000) ∧
    -Real.log (427487 / 500000) ≤ (7834211 / 50000000) := by
  have h := checkLog_sound (w := (72513 / 927487)) (n := 12)
    (lo := (156684219 / 1000000000)) (hi := (7834211 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427487) = 1/(427487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7834211 / 50000000) (-156684219 / 1000000000) (Real.log (427487 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135696297 / 1000000000) ≤ -Real.log (500000 / 572667) ∧
    -Real.log (500000 / 572667) ≤ (67848149 / 500000000) := by
  have h := checkLog_sound (w := (72667 / 1072667)) (n := 12)
    (lo := (135696297 / 1000000000)) (hi := (67848149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572667 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572667 / 500000) = 1/(500000 / 572667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135696297 / 1000000000) (67848149 / 500000000) (Real.log (572667 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (572667 / 500000) = -Real.log (500000 / 572667) := by
    rw [show ((572667 / 500000) : ℝ) = ((500000 / 572667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (157044529 / 1000000000) ≤ -Real.log (427333 / 500000) ∧
    -Real.log (427333 / 500000) ≤ (15704453 / 100000000) := by
  have h := checkLog_sound (w := (72667 / 927333)) (n := 12)
    (lo := (157044529 / 1000000000)) (hi := (15704453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427333) = 1/(427333 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15704453 / 100000000) (-157044529 / 1000000000) (Real.log (427333 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (587847429 / 1000000000) ≤ -Real.log (125000000000 / 225013672409) ∧
    -Real.log (125000000000 / 225013672409) ≤ (58784743 / 100000000) := by
  have h := checkLog_sound (w := (100013672409 / 350013672409)) (n := 12)
    (lo := (587847429 / 1000000000)) (hi := (58784743 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225013672409 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225013672409 / 125000000000) = 1/(125000000000 / 225013672409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (587847429 / 1000000000) (58784743 / 100000000) (Real.log (225013672409 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (225013672409 / 125000000000) = -Real.log (125000000000 / 225013672409) := by
    rw [show ((225013672409 / 125000000000) : ℝ) = ((125000000000 / 225013672409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23564949 / 40000000) ≤ -Real.log (20000000000 / 36048166393) ∧
    -Real.log (20000000000 / 36048166393) ≤ (294561863 / 500000000) := by
  have h := checkLog_sound (w := (16048166393 / 56048166393)) (n := 12)
    (lo := (23564949 / 40000000)) (hi := (294561863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36048166393 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36048166393 / 20000000000) = 1/(20000000000 / 36048166393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (23564949 / 40000000) (294561863 / 500000000) (Real.log (36048166393 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (36048166393 / 20000000000) = -Real.log (20000000000 / 36048166393) := by
    rw [show ((36048166393 / 20000000000) : ℝ) = ((20000000000 / 36048166393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (411220517 / 1000000000) ≤ -Real.log (500000000000 / 754329002971) ∧
    -Real.log (500000000000 / 754329002971) ≤ (205610259 / 500000000) := by
  have h := checkLog_sound (w := (254329002971 / 1254329002971)) (n := 12)
    (lo := (411220517 / 1000000000)) (hi := (205610259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754329002971 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754329002971 / 500000000000) = 1/(500000000000 / 754329002971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (411220517 / 1000000000) (205610259 / 500000000) (Real.log (754329002971 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (754329002971 / 500000000000) = -Real.log (500000000000 / 754329002971) := by
    rw [show ((754329002971 / 500000000000) : ℝ) = ((500000000000 / 754329002971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41209661 / 100000000) ≤ -Real.log (500000000000 / 754990154603) ∧
    -Real.log (500000000000 / 754990154603) ≤ (412096611 / 1000000000) := by
  have h := checkLog_sound (w := (254990154603 / 1254990154603)) (n := 12)
    (lo := (41209661 / 100000000)) (hi := (412096611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754990154603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754990154603 / 500000000000) = 1/(500000000000 / 754990154603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (41209661 / 100000000) (412096611 / 1000000000) (Real.log (754990154603 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (754990154603 / 500000000000) = -Real.log (500000000000 / 754990154603) := by
    rw [show ((754990154603 / 500000000000) : ℝ) = ((500000000000 / 754990154603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (73027891 / 250000000) ≤ -Real.log (100000000000 / 133925242171) ∧
    -Real.log (100000000000 / 133925242171) ≤ (58422313 / 200000000) := by
  have h := checkLog_sound (w := (33925242171 / 233925242171)) (n := 12)
    (lo := (73027891 / 250000000)) (hi := (58422313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133925242171 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133925242171 / 100000000000) = 1/(100000000000 / 133925242171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (73027891 / 250000000) (58422313 / 200000000) (Real.log (133925242171 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (133925242171 / 100000000000) = -Real.log (100000000000 / 133925242171) := by
    rw [show ((133925242171 / 100000000000) : ℝ) = ((100000000000 / 133925242171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (292740827 / 1000000000) ≤ -Real.log (250000000000 / 335023857273) ∧
    -Real.log (250000000000 / 335023857273) ≤ (73185207 / 250000000) := by
  have h := checkLog_sound (w := (85023857273 / 585023857273)) (n := 12)
    (lo := (292740827 / 1000000000)) (hi := (73185207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335023857273 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335023857273 / 250000000000) = 1/(250000000000 / 335023857273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (292740827 / 1000000000) (73185207 / 250000000) (Real.log (335023857273 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (335023857273 / 250000000000) = -Real.log (250000000000 / 335023857273) := by
    rw [show ((335023857273 / 250000000000) : ℝ) = ((250000000000 / 335023857273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2668529 / 125000000) ≤ -Real.log (244719507111 / 250000000000) ∧
    -Real.log (244719507111 / 250000000000) ≤ (21348233 / 1000000000) := by
  have h := checkLog_sound (w := (5280492889 / 494719507111)) (n := 12)
    (lo := (2668529 / 125000000)) (hi := (21348233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244719507111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244719507111) = 1/(244719507111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21348233 / 1000000000) (-2668529 / 125000000) (Real.log (244719507111 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34011 / 1600000) ≤ -Real.log (244741864831 / 250000000000) ∧
    -Real.log (244741864831 / 250000000000) ≤ (5314219 / 250000000) := by
  have h := checkLog_sound (w := (5258135169 / 494741864831)) (n := 12)
    (lo := (34011 / 1600000)) (hi := (5314219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244741864831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244741864831) = 1/(244741864831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5314219 / 250000000) (-34011 / 1600000) (Real.log (244741864831 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell061

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell062Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell062
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (15765447 / 62500000) ≤ -Real.log (5120 / 6589) ∧
    -Real.log (5120 / 6589) ≤ (252247153 / 1000000000) := by
  have h := checkLog_sound (w := (1469 / 11709)) (n := 12)
    (lo := (15765447 / 62500000)) (hi := (252247153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6589 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6589 / 5120) = 1/(5120 / 6589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (15765447 / 62500000) (252247153 / 1000000000) (Real.log (6589 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6589 / 5120) = -Real.log (5120 / 6589) := by
    rw [show ((6589 / 5120) : ℝ) = ((5120 / 6589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (42269167 / 125000000) ≤ -Real.log (3651 / 5120) ∧
    -Real.log (3651 / 5120) ≤ (338153337 / 1000000000) := by
  have h := checkLog_sound (w := (1469 / 8771)) (n := 12)
    (lo := (42269167 / 125000000)) (hi := (338153337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3651) = 1/(3651 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-338153337 / 1000000000) (-42269167 / 125000000) (Real.log (3651 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1967123 / 7812500) ≤ -Real.log (2560 / 3293) ∧
    -Real.log (2560 / 3293) ≤ (50358349 / 200000000) := by
  have h := checkLog_sound (w := (733 / 5853)) (n := 12)
    (lo := (1967123 / 7812500)) (hi := (50358349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3293 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3293 / 2560) = 1/(2560 / 3293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (1967123 / 7812500) (50358349 / 200000000) (Real.log (3293 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3293 / 2560) = -Real.log (2560 / 3293) := by
    rw [show ((3293 / 2560) : ℝ) = ((2560 / 3293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (337331981 / 1000000000) ≤ -Real.log (1827 / 2560) ∧
    -Real.log (1827 / 2560) ≤ (168665991 / 500000000) := by
  have h := checkLog_sound (w := (733 / 4387)) (n := 12)
    (lo := (337331981 / 1000000000)) (hi := (168665991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1827) = 1/(1827 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-168665991 / 500000000) (-337331981 / 1000000000) (Real.log (1827 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184968051 / 1000000000) ≤ -Real.log (50000 / 60159) ∧
    -Real.log (50000 / 60159) ≤ (46242013 / 250000000) := by
  have h := checkLog_sound (w := (10159 / 110159)) (n := 12)
    (lo := (184968051 / 1000000000)) (hi := (46242013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60159 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60159 / 50000) = 1/(50000 / 60159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184968051 / 1000000000) (46242013 / 250000000) (Real.log (60159 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (60159 / 50000) = -Real.log (50000 / 60159) := by
    rw [show ((60159 / 50000) : ℝ) = ((50000 / 60159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28390809 / 125000000) ≤ -Real.log (39841 / 50000) ∧
    -Real.log (39841 / 50000) ≤ (227126473 / 1000000000) := by
  have h := checkLog_sound (w := (10159 / 89841)) (n := 12)
    (lo := (28390809 / 125000000)) (hi := (227126473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39841) = 1/(39841 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-227126473 / 1000000000) (-28390809 / 125000000) (Real.log (39841 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37063413 / 200000000) ≤ -Real.log (2500 / 3009) ∧
    -Real.log (2500 / 3009) ≤ (92658533 / 500000000) := by
  have h := checkLog_sound (w := (509 / 5509)) (n := 12)
    (lo := (37063413 / 200000000)) (hi := (92658533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3009 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3009 / 2500) = 1/(2500 / 3009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37063413 / 200000000) (92658533 / 500000000) (Real.log (3009 / 2500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3009 / 2500) = -Real.log (2500 / 3009) := by
    rw [show ((3009 / 2500) : ℝ) = ((2500 / 3009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (113826853 / 500000000) ≤ -Real.log (1991 / 2500) ∧
    -Real.log (1991 / 2500) ≤ (227653707 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 4491)) (n := 12)
    (lo := (113826853 / 500000000)) (hi := (227653707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1991) = 1/(1991 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-227653707 / 1000000000) (-113826853 / 500000000) (Real.log (1991 / 2500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2120241 / 15625000) ≤ -Real.log (1000000 / 1145333) ∧
    -Real.log (1000000 / 1145333) ≤ (5427817 / 40000000) := by
  have h := checkLog_sound (w := (145333 / 2145333)) (n := 12)
    (lo := (2120241 / 15625000)) (hi := (5427817 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145333 / 1000000) = 1/(1000000 / 1145333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2120241 / 15625000) (5427817 / 40000000) (Real.log (1145333 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1145333 / 1000000) = -Real.log (1000000 / 1145333) := by
    rw [show ((1145333 / 1000000) : ℝ) = ((1000000 / 1145333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (157043359 / 1000000000) ≤ -Real.log (854667 / 1000000) ∧
    -Real.log (854667 / 1000000) ≤ (981521 / 6250000) := by
  have h := checkLog_sound (w := (145333 / 1854667)) (n := 12)
    (lo := (157043359 / 1000000000)) (hi := (981521 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854667) = 1/(854667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-981521 / 6250000) (-157043359 / 1000000000) (Real.log (854667 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16995429 / 125000000) ≤ -Real.log (25000 / 28641) ∧
    -Real.log (25000 / 28641) ≤ (135963433 / 1000000000) := by
  have h := checkLog_sound (w := (3641 / 53641)) (n := 12)
    (lo := (16995429 / 125000000)) (hi := (135963433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28641 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28641 / 25000) = 1/(25000 / 28641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16995429 / 125000000) (135963433 / 1000000000) (Real.log (28641 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (28641 / 25000) = -Real.log (25000 / 28641) := by
    rw [show ((28641 / 25000) : ℝ) = ((25000 / 28641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39350657 / 250000000) ≤ -Real.log (21359 / 25000) ∧
    -Real.log (21359 / 25000) ≤ (157402629 / 1000000000) := by
  have h := checkLog_sound (w := (3641 / 46359)) (n := 12)
    (lo := (39350657 / 250000000)) (hi := (157402629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21359) = 1/(21359 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-157402629 / 1000000000) (-39350657 / 250000000) (Real.log (21359 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23564949 / 40000000) ≤ -Real.log (31250000000 / 56325259989) ∧
    -Real.log (31250000000 / 56325259989) ≤ (294561863 / 500000000) := by
  have h := checkLog_sound (w := (25075259989 / 87575259989)) (n := 12)
    (lo := (23564949 / 40000000)) (hi := (294561863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56325259989 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56325259989 / 31250000000) = 1/(31250000000 / 56325259989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23564949 / 40000000) (294561863 / 500000000) (Real.log (56325259989 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (56325259989 / 31250000000) = -Real.log (31250000000 / 56325259989) := by
    rw [show ((56325259989 / 31250000000) : ℝ) = ((31250000000 / 56325259989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (590400489 / 1000000000) ≤ -Real.log (125000000000 / 225588879759) ∧
    -Real.log (125000000000 / 225588879759) ≤ (59040049 / 100000000) := by
  have h := checkLog_sound (w := (100588879759 / 350588879759)) (n := 12)
    (lo := (590400489 / 1000000000)) (hi := (59040049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225588879759 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225588879759 / 125000000000) = 1/(125000000000 / 225588879759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (590400489 / 1000000000) (59040049 / 100000000) (Real.log (225588879759 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (225588879759 / 125000000000) = -Real.log (125000000000 / 225588879759) := by
    rw [show ((225588879759 / 125000000000) : ℝ) = ((125000000000 / 225588879759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (103023631 / 250000000) ≤ -Real.log (500000000000 / 754988579603) ∧
    -Real.log (500000000000 / 754988579603) ≤ (16483781 / 40000000) := by
  have h := checkLog_sound (w := (254988579603 / 1254988579603)) (n := 12)
    (lo := (103023631 / 250000000)) (hi := (16483781 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754988579603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754988579603 / 500000000000) = 1/(500000000000 / 754988579603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103023631 / 250000000) (16483781 / 40000000) (Real.log (754988579603 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (754988579603 / 500000000000) = -Real.log (500000000000 / 754988579603) := by
    rw [show ((754988579603 / 500000000000) : ℝ) = ((500000000000 / 754988579603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103242693 / 250000000) ≤ -Real.log (250000000000 / 377825213461) ∧
    -Real.log (250000000000 / 377825213461) ≤ (412970773 / 1000000000) := by
  have h := checkLog_sound (w := (127825213461 / 627825213461)) (n := 12)
    (lo := (103242693 / 250000000)) (hi := (412970773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377825213461 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377825213461 / 250000000000) = 1/(250000000000 / 377825213461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103242693 / 250000000) (412970773 / 1000000000) (Real.log (377825213461 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (377825213461 / 250000000000) = -Real.log (250000000000 / 377825213461) := by
    rw [show ((377825213461 / 250000000000) : ℝ) = ((250000000000 / 377825213461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9148087 / 31250000) ≤ -Real.log (100000000000 / 134009269107) ∧
    -Real.log (100000000000 / 134009269107) ≤ (58547757 / 200000000) := by
  have h := checkLog_sound (w := (34009269107 / 234009269107)) (n := 12)
    (lo := (9148087 / 31250000)) (hi := (58547757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134009269107 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134009269107 / 100000000000) = 1/(100000000000 / 134009269107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9148087 / 31250000) (58547757 / 200000000) (Real.log (134009269107 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (134009269107 / 100000000000) = -Real.log (100000000000 / 134009269107) := by
    rw [show ((134009269107 / 100000000000) : ℝ) = ((100000000000 / 134009269107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (293366061 / 1000000000) ≤ -Real.log (500000000000 / 670466782153) ∧
    -Real.log (500000000000 / 670466782153) ≤ (146683031 / 500000000) := by
  have h := checkLog_sound (w := (170466782153 / 1170466782153)) (n := 12)
    (lo := (293366061 / 1000000000)) (hi := (146683031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670466782153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670466782153 / 500000000000) = 1/(500000000000 / 670466782153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (293366061 / 1000000000) (146683031 / 500000000) (Real.log (670466782153 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (670466782153 / 500000000000) = -Real.log (500000000000 / 670466782153) := by
    rw [show ((670466782153 / 500000000000) : ℝ) = ((500000000000 / 670466782153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4287839 / 200000000) ≤ -Real.log (611743119 / 625000000) ∧
    -Real.log (611743119 / 625000000) ≤ (5359799 / 250000000) := by
  have h := checkLog_sound (w := (13256881 / 1236743119)) (n := 12)
    (lo := (4287839 / 200000000)) (hi := (5359799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 611743119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 611743119) = 1/(611743119 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5359799 / 250000000) (-4287839 / 200000000) (Real.log (611743119 / 625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4269587 / 200000000) ≤ -Real.log (978878319111 / 1000000000000) ∧
    -Real.log (978878319111 / 1000000000000) ≤ (667123 / 31250000) := by
  have h := checkLog_sound (w := (21121680889 / 1978878319111)) (n := 12)
    (lo := (4269587 / 200000000)) (hi := (667123 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978878319111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978878319111) = 1/(978878319111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-667123 / 31250000) (-4269587 / 200000000) (Real.log (978878319111 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell062

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell063Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell063
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (252702353 / 1000000000) ≤ -Real.log (80 / 103) ∧
    -Real.log (80 / 103) ≤ (126351177 / 500000000) := by
  have h := checkLog_sound (w := (23 / 183)) (n := 12)
    (lo := (252702353 / 1000000000)) (hi := (126351177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103 / 80) = 1/(80 / 103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (252702353 / 1000000000) (126351177 / 500000000) (Real.log (103 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (103 / 80) = -Real.log (80 / 103) := by
    rw [show ((103 / 80) : ℝ) = ((80 / 103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (169487683 / 500000000) ≤ -Real.log (57 / 80) ∧
    -Real.log (57 / 80) ≤ (338975367 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 57) = 1/(57 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-338975367 / 1000000000) (-169487683 / 500000000) (Real.log (57 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (15765447 / 62500000) ≤ -Real.log (5120 / 6589) ∧
    -Real.log (5120 / 6589) ≤ (252247153 / 1000000000) := by
  have h := checkLog_sound (w := (1469 / 11709)) (n := 12)
    (lo := (15765447 / 62500000)) (hi := (252247153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6589 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6589 / 5120) = 1/(5120 / 6589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (15765447 / 62500000) (252247153 / 1000000000) (Real.log (6589 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6589 / 5120) = -Real.log (5120 / 6589) := by
    rw [show ((6589 / 5120) : ℝ) = ((5120 / 6589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (42269167 / 125000000) ≤ -Real.log (3651 / 5120) ∧
    -Real.log (3651 / 5120) ≤ (338153337 / 1000000000) := by
  have h := checkLog_sound (w := (1469 / 8771)) (n := 12)
    (lo := (42269167 / 125000000)) (hi := (338153337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3651) = 1/(3651 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-338153337 / 1000000000) (-42269167 / 125000000) (Real.log (3651 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (92658117 / 500000000) ≤ -Real.log (1000000 / 1203599) ∧
    -Real.log (1000000 / 1203599) ≤ (37063247 / 200000000) := by
  have h := checkLog_sound (w := (203599 / 2203599)) (n := 12)
    (lo := (92658117 / 500000000)) (hi := (37063247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203599 / 1000000) = 1/(1000000 / 1203599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (92658117 / 500000000) (37063247 / 200000000) (Real.log (1203599 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1203599 / 1000000) = -Real.log (1000000 / 1203599) := by
    rw [show ((1203599 / 1000000) : ℝ) = ((1000000 / 1203599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (227652451 / 1000000000) ≤ -Real.log (796401 / 1000000) ∧
    -Real.log (796401 / 1000000) ≤ (56913113 / 250000000) := by
  have h := checkLog_sound (w := (203599 / 1796401)) (n := 12)
    (lo := (227652451 / 1000000000)) (hi := (56913113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796401) = 1/(796401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-56913113 / 250000000) (-227652451 / 1000000000) (Real.log (796401 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (185665127 / 1000000000) ≤ -Real.log (1000000 / 1204019) ∧
    -Real.log (1000000 / 1204019) ≤ (23208141 / 125000000) := by
  have h := checkLog_sound (w := (204019 / 2204019)) (n := 12)
    (lo := (185665127 / 1000000000)) (hi := (23208141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204019 / 1000000) = 1/(1000000 / 1204019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (185665127 / 1000000000) (23208141 / 125000000) (Real.log (1204019 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1204019 / 1000000) = -Real.log (1000000 / 1204019) := by
    rw [show ((1204019 / 1000000) : ℝ) = ((1000000 / 1204019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114089981 / 500000000) ≤ -Real.log (795981 / 1000000) ∧
    -Real.log (795981 / 1000000) ≤ (228179963 / 1000000000) := by
  have h := checkLog_sound (w := (204019 / 1795981)) (n := 12)
    (lo := (114089981 / 500000000)) (hi := (228179963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795981) = 1/(795981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-228179963 / 1000000000) (-114089981 / 500000000) (Real.log (795981 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135962559 / 1000000000) ≤ -Real.log (1000000 / 1145639) ∧
    -Real.log (1000000 / 1145639) ≤ (424883 / 3125000) := by
  have h := checkLog_sound (w := (145639 / 2145639)) (n := 12)
    (lo := (135962559 / 1000000000)) (hi := (424883 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145639 / 1000000) = 1/(1000000 / 1145639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135962559 / 1000000000) (424883 / 3125000) (Real.log (1145639 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1145639 / 1000000) = -Real.log (1000000 / 1145639) := by
    rw [show ((1145639 / 1000000) : ℝ) = ((1000000 / 1145639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (157401457 / 1000000000) ≤ -Real.log (854361 / 1000000) ∧
    -Real.log (854361 / 1000000) ≤ (78700729 / 500000000) := by
  have h := checkLog_sound (w := (145639 / 1854361)) (n := 12)
    (lo := (157401457 / 1000000000)) (hi := (78700729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854361) = 1/(854361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-78700729 / 500000000) (-157401457 / 1000000000) (Real.log (854361 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136231369 / 1000000000) ≤ -Real.log (1000000 / 1145947) ∧
    -Real.log (1000000 / 1145947) ≤ (13623137 / 100000000) := by
  have h := checkLog_sound (w := (145947 / 2145947)) (n := 12)
    (lo := (136231369 / 1000000000)) (hi := (13623137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145947 / 1000000) = 1/(1000000 / 1145947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136231369 / 1000000000) (13623137 / 100000000) (Real.log (1145947 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1145947 / 1000000) = -Real.log (1000000 / 1145947) := by
    rw [show ((1145947 / 1000000) : ℝ) = ((1000000 / 1145947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (78881013 / 500000000) ≤ -Real.log (854053 / 1000000) ∧
    -Real.log (854053 / 1000000) ≤ (157762027 / 1000000000) := by
  have h := checkLog_sound (w := (145947 / 1854053)) (n := 12)
    (lo := (78881013 / 500000000)) (hi := (157762027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854053) = 1/(854053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-157762027 / 1000000000) (-78881013 / 500000000) (Real.log (854053 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (590400489 / 1000000000) ≤ -Real.log (100000000000 / 180471103807) ∧
    -Real.log (100000000000 / 180471103807) ≤ (59040049 / 100000000) := by
  have h := checkLog_sound (w := (80471103807 / 280471103807)) (n := 12)
    (lo := (590400489 / 1000000000)) (hi := (59040049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180471103807 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180471103807 / 100000000000) = 1/(100000000000 / 180471103807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (590400489 / 1000000000) (59040049 / 100000000) (Real.log (180471103807 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (180471103807 / 100000000000) = -Real.log (100000000000 / 180471103807) := by
    rw [show ((180471103807 / 100000000000) : ℝ) = ((100000000000 / 180471103807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (14791943 / 25000000) ≤ -Real.log (50000000000 / 90350877193) ∧
    -Real.log (50000000000 / 90350877193) ≤ (591677721 / 1000000000) := by
  have h := checkLog_sound (w := (40350877193 / 140350877193)) (n := 12)
    (lo := (14791943 / 25000000)) (hi := (591677721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90350877193 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90350877193 / 50000000000) = 1/(50000000000 / 90350877193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (14791943 / 25000000) (591677721 / 1000000000) (Real.log (90350877193 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (90350877193 / 50000000000) = -Real.log (50000000000 / 90350877193) := by
    rw [show ((90350877193 / 50000000000) : ℝ) = ((50000000000 / 90350877193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (206484343 / 500000000) ≤ -Real.log (100000000000 / 151129770053) ∧
    -Real.log (100000000000 / 151129770053) ≤ (412968687 / 1000000000) := by
  have h := checkLog_sound (w := (51129770053 / 251129770053)) (n := 12)
    (lo := (206484343 / 500000000)) (hi := (412968687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151129770053 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151129770053 / 100000000000) = 1/(100000000000 / 151129770053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206484343 / 500000000) (412968687 / 1000000000) (Real.log (151129770053 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (151129770053 / 100000000000) = -Real.log (100000000000 / 151129770053) := by
    rw [show ((151129770053 / 100000000000) : ℝ) = ((100000000000 / 151129770053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41384509 / 100000000) ≤ -Real.log (7812500000 / 11817365537) ∧
    -Real.log (7812500000 / 11817365537) ≤ (413845091 / 1000000000) := by
  have h := checkLog_sound (w := (4004865537 / 19629865537)) (n := 12)
    (lo := (41384509 / 100000000)) (hi := (413845091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11817365537 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11817365537 / 7812500000) = 1/(7812500000 / 11817365537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (41384509 / 100000000) (413845091 / 1000000000) (Real.log (11817365537 / 7812500000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (11817365537 / 7812500000) = -Real.log (7812500000 / 11817365537) := by
    rw [show ((11817365537 / 7812500000) : ℝ) = ((7812500000 / 11817365537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (293364017 / 1000000000) ≤ -Real.log (500000000000 / 670465412161) ∧
    -Real.log (500000000000 / 670465412161) ≤ (146682009 / 500000000) := by
  have h := checkLog_sound (w := (170465412161 / 1170465412161)) (n := 12)
    (lo := (293364017 / 1000000000)) (hi := (146682009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670465412161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670465412161 / 500000000000) = 1/(500000000000 / 670465412161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (293364017 / 1000000000) (146682009 / 500000000) (Real.log (670465412161 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (670465412161 / 500000000000) = -Real.log (500000000000 / 670465412161) := by
    rw [show ((670465412161 / 500000000000) : ℝ) = ((500000000000 / 670465412161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (58798679 / 200000000) ≤ -Real.log (500000000000 / 670887521033) ∧
    -Real.log (500000000000 / 670887521033) ≤ (73498349 / 250000000) := by
  have h := checkLog_sound (w := (170887521033 / 1170887521033)) (n := 12)
    (lo := (58798679 / 200000000)) (hi := (73498349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670887521033 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670887521033 / 500000000000) = 1/(500000000000 / 670887521033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (58798679 / 200000000) (73498349 / 250000000) (Real.log (670887521033 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (670887521033 / 500000000000) = -Real.log (500000000000 / 670887521033) := by
    rw [show ((670887521033 / 500000000000) : ℝ) = ((500000000000 / 670887521033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (672833 / 31250000) ≤ -Real.log (978699473191 / 1000000000000) ∧
    -Real.log (978699473191 / 1000000000000) ≤ (21530657 / 1000000000) := by
  have h := checkLog_sound (w := (21300526809 / 1978699473191)) (n := 12)
    (lo := (672833 / 31250000)) (hi := (21530657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978699473191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978699473191) = 1/(978699473191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21530657 / 1000000000) (-672833 / 31250000) (Real.log (978699473191 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21438897 / 1000000000) ≤ -Real.log (978789281679 / 1000000000000) ∧
    -Real.log (978789281679 / 1000000000000) ≤ (10719449 / 500000000) := by
  have h := checkLog_sound (w := (21210718321 / 1978789281679)) (n := 12)
    (lo := (21438897 / 1000000000)) (hi := (10719449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978789281679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978789281679) = 1/(978789281679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10719449 / 500000000) (-21438897 / 1000000000) (Real.log (978789281679 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell063

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell064Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell064
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (253157347 / 1000000000) ≤ -Real.log (1024 / 1319) ∧
    -Real.log (1024 / 1319) ≤ (63289337 / 250000000) := by
  have h := checkLog_sound (w := (295 / 2343)) (n := 12)
    (lo := (253157347 / 1000000000)) (hi := (63289337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319 / 1024) = 1/(1024 / 1319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253157347 / 1000000000) (63289337 / 250000000) (Real.log (1319 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1319 / 1024) = -Real.log (1024 / 1319) := by
    rw [show ((1319 / 1024) : ℝ) = ((1024 / 1319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (339798073 / 1000000000) ≤ -Real.log (729 / 1024) ∧
    -Real.log (729 / 1024) ≤ (169899037 / 500000000) := by
  have h := checkLog_sound (w := (295 / 1753)) (n := 12)
    (lo := (339798073 / 1000000000)) (hi := (169899037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 729) = 1/(729 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-169899037 / 500000000) (-339798073 / 1000000000) (Real.log (729 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (252702353 / 1000000000) ≤ -Real.log (80 / 103) ∧
    -Real.log (80 / 103) ≤ (126351177 / 500000000) := by
  have h := checkLog_sound (w := (23 / 183)) (n := 12)
    (lo := (252702353 / 1000000000)) (hi := (126351177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103 / 80) = 1/(80 / 103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (252702353 / 1000000000) (126351177 / 500000000) (Real.log (103 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (103 / 80) = -Real.log (80 / 103) := by
    rw [show ((103 / 80) : ℝ) = ((80 / 103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (169487683 / 500000000) ≤ -Real.log (57 / 80) ∧
    -Real.log (57 / 80) ≤ (338975367 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 57) = 1/(57 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-338975367 / 1000000000) (-169487683 / 500000000) (Real.log (57 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23208037 / 125000000) ≤ -Real.log (500000 / 602009) ∧
    -Real.log (500000 / 602009) ≤ (185664297 / 1000000000) := by
  have h := checkLog_sound (w := (102009 / 1102009)) (n := 12)
    (lo := (23208037 / 125000000)) (hi := (185664297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602009 / 500000) = 1/(500000 / 602009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23208037 / 125000000) (185664297 / 1000000000) (Real.log (602009 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (602009 / 500000) = -Real.log (500000 / 602009) := by
    rw [show ((602009 / 500000) : ℝ) = ((500000 / 602009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114089353 / 500000000) ≤ -Real.log (397991 / 500000) ∧
    -Real.log (397991 / 500000) ≤ (228178707 / 1000000000) := by
  have h := checkLog_sound (w := (102009 / 897991)) (n := 12)
    (lo := (114089353 / 500000000)) (hi := (228178707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397991) = 1/(397991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-228178707 / 1000000000) (-114089353 / 500000000) (Real.log (397991 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46503267 / 250000000) ≤ -Real.log (500000 / 602219) ∧
    -Real.log (500000 / 602219) ≤ (186013069 / 1000000000) := by
  have h := checkLog_sound (w := (102219 / 1102219)) (n := 12)
    (lo := (46503267 / 250000000)) (hi := (186013069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602219 / 500000) = 1/(500000 / 602219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46503267 / 250000000) (186013069 / 1000000000) (Real.log (602219 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (602219 / 500000) = -Real.log (500000 / 602219) := by
    rw [show ((602219 / 500000) : ℝ) = ((500000 / 602219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (45741299 / 200000000) ≤ -Real.log (397781 / 500000) ∧
    -Real.log (397781 / 500000) ≤ (3573539 / 15625000) := by
  have h := checkLog_sound (w := (102219 / 897781)) (n := 12)
    (lo := (45741299 / 200000000)) (hi := (3573539 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397781) = 1/(397781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3573539 / 15625000) (-45741299 / 200000000) (Real.log (397781 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4257203 / 31250000) ≤ -Real.log (500000 / 572973) ∧
    -Real.log (500000 / 572973) ≤ (136230497 / 1000000000) := by
  have h := checkLog_sound (w := (72973 / 1072973)) (n := 12)
    (lo := (4257203 / 31250000)) (hi := (136230497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572973 / 500000) = 1/(500000 / 572973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4257203 / 31250000) (136230497 / 1000000000) (Real.log (572973 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (572973 / 500000) = -Real.log (500000 / 572973) := by
    rw [show ((572973 / 500000) : ℝ) = ((500000 / 572973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31552171 / 200000000) ≤ -Real.log (427027 / 500000) ∧
    -Real.log (427027 / 500000) ≤ (19720107 / 125000000) := by
  have h := checkLog_sound (w := (72973 / 927027)) (n := 12)
    (lo := (31552171 / 200000000)) (hi := (19720107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427027) = 1/(427027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19720107 / 125000000) (-31552171 / 200000000) (Real.log (427027 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136498361 / 1000000000) ≤ -Real.log (1000000 / 1146253) ∧
    -Real.log (1000000 / 1146253) ≤ (68249181 / 500000000) := by
  have h := checkLog_sound (w := (146253 / 2146253)) (n := 12)
    (lo := (136498361 / 1000000000)) (hi := (68249181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146253 / 1000000) = 1/(1000000 / 1146253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136498361 / 1000000000) (68249181 / 500000000) (Real.log (1146253 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1146253 / 1000000) = -Real.log (1000000 / 1146253) := by
    rw [show ((1146253 / 1000000) : ℝ) = ((1000000 / 1146253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79060191 / 500000000) ≤ -Real.log (853747 / 1000000) ∧
    -Real.log (853747 / 1000000) ≤ (158120383 / 1000000000) := by
  have h := checkLog_sound (w := (146253 / 1853747)) (n := 12)
    (lo := (79060191 / 500000000)) (hi := (158120383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853747) = 1/(853747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-158120383 / 1000000000) (-79060191 / 500000000) (Real.log (853747 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (14791943 / 25000000) ≤ -Real.log (500000000000 / 903508771929) ∧
    -Real.log (500000000000 / 903508771929) ≤ (591677721 / 1000000000) := by
  have h := checkLog_sound (w := (403508771929 / 1403508771929)) (n := 12)
    (lo := (14791943 / 25000000)) (hi := (591677721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903508771929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903508771929 / 500000000000) = 1/(500000000000 / 903508771929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (14791943 / 25000000) (591677721 / 1000000000) (Real.log (903508771929 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (903508771929 / 500000000000) = -Real.log (500000000000 / 903508771929) := by
    rw [show ((903508771929 / 500000000000) : ℝ) = ((500000000000 / 903508771929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29647771 / 50000000) ≤ -Real.log (500000000000 / 904663923183) ∧
    -Real.log (500000000000 / 904663923183) ≤ (592955421 / 1000000000) := by
  have h := checkLog_sound (w := (404663923183 / 1404663923183)) (n := 12)
    (lo := (29647771 / 50000000)) (hi := (592955421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904663923183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904663923183 / 500000000000) = 1/(500000000000 / 904663923183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (29647771 / 50000000) (592955421 / 1000000000) (Real.log (904663923183 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (904663923183 / 500000000000) = -Real.log (500000000000 / 904663923183) := by
    rw [show ((904663923183 / 500000000000) : ℝ) = ((500000000000 / 904663923183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (413843003 / 1000000000) ≤ -Real.log (500000000000 / 756309816051) ∧
    -Real.log (500000000000 / 756309816051) ≤ (103460751 / 250000000) := by
  have h := checkLog_sound (w := (256309816051 / 1256309816051)) (n := 12)
    (lo := (413843003 / 1000000000)) (hi := (103460751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756309816051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756309816051 / 500000000000) = 1/(500000000000 / 756309816051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (413843003 / 1000000000) (103460751 / 250000000) (Real.log (756309816051 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (756309816051 / 500000000000) = -Real.log (500000000000 / 756309816051) := by
    rw [show ((756309816051 / 500000000000) : ℝ) = ((500000000000 / 756309816051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (414719563 / 1000000000) ≤ -Real.log (12500000000 / 18924326451) ∧
    -Real.log (12500000000 / 18924326451) ≤ (103679891 / 250000000) := by
  have h := checkLog_sound (w := (6424326451 / 31424326451)) (n := 12)
    (lo := (414719563 / 1000000000)) (hi := (103679891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18924326451 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18924326451 / 12500000000) = 1/(12500000000 / 18924326451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (414719563 / 1000000000) (103679891 / 250000000) (Real.log (18924326451 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (18924326451 / 12500000000) = -Real.log (12500000000 / 18924326451) := by
    rw [show ((18924326451 / 12500000000) : ℝ) = ((12500000000 / 18924326451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (36748919 / 125000000) ≤ -Real.log (62500000000 / 83860768757) ∧
    -Real.log (62500000000 / 83860768757) ≤ (293991353 / 1000000000) := by
  have h := checkLog_sound (w := (21360768757 / 146360768757)) (n := 12)
    (lo := (36748919 / 125000000)) (hi := (293991353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83860768757 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83860768757 / 62500000000) = 1/(62500000000 / 83860768757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36748919 / 125000000) (293991353 / 1000000000) (Real.log (83860768757 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (83860768757 / 62500000000) = -Real.log (62500000000 / 83860768757) := by
    rw [show ((83860768757 / 62500000000) : ℝ) = ((62500000000 / 83860768757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (294618743 / 1000000000) ≤ -Real.log (250000000000 / 335653595269) ∧
    -Real.log (250000000000 / 335653595269) ≤ (36827343 / 125000000) := by
  have h := checkLog_sound (w := (85653595269 / 585653595269)) (n := 12)
    (lo := (294618743 / 1000000000)) (hi := (36827343 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335653595269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335653595269 / 250000000000) = 1/(250000000000 / 335653595269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (294618743 / 1000000000) (36827343 / 125000000) (Real.log (335653595269 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (335653595269 / 250000000000) = -Real.log (250000000000 / 335653595269) := by
    rw [show ((335653595269 / 250000000000) : ℝ) = ((250000000000 / 335653595269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1081101 / 50000000) ≤ -Real.log (978610059991 / 1000000000000) ∧
    -Real.log (978610059991 / 1000000000000) ≤ (21622021 / 1000000000) := by
  have h := checkLog_sound (w := (21389940009 / 1978610059991)) (n := 12)
    (lo := (1081101 / 50000000)) (hi := (21622021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978610059991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978610059991) = 1/(978610059991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21622021 / 1000000000) (-1081101 / 50000000) (Real.log (978610059991 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10765179 / 500000000) ≤ -Real.log (244674941271 / 250000000000) ∧
    -Real.log (244674941271 / 250000000000) ≤ (21530359 / 1000000000) := by
  have h := checkLog_sound (w := (5325058729 / 494674941271)) (n := 12)
    (lo := (10765179 / 500000000)) (hi := (21530359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244674941271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244674941271) = 1/(244674941271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21530359 / 1000000000) (-10765179 / 500000000) (Real.log (244674941271 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell064

end


