-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell239Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell239Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:56:17.279121+00:00
-- url     : https://prove2.me/theorems/aea93ce2-b3bd-4f35-8059-78d05851defe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell239Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell240…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell239Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell240Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell241Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell242Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell243Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell244Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell239Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell240Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell241Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell242Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell243Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell244Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell239Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell240Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell241Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell242Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell243Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell244Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell239Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell240Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell241Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell242Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell243Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell244Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell239Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell239
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

theorem reflection_log_1_neg : (164876643 / 500000000) ≤ -Real.log (64 / 89) ∧
    -Real.log (64 / 89) ≤ (329753287 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 153)) (n := 12)
    (lo := (164876643 / 500000000)) (hi := (329753287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89 / 64) = 1/(64 / 89) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164876643 / 500000000) (329753287 / 1000000000) (Real.log (89 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (89 / 64) = -Real.log (64 / 89) := by
    rw [show ((89 / 64) : ℝ) = ((64 / 89) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (495321437 / 1000000000) ≤ -Real.log (39 / 64) ∧
    -Real.log (39 / 64) ≤ (247660719 / 500000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 39) = 1/(39 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-247660719 / 500000000) (-495321437 / 1000000000) (Real.log (39 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (329331849 / 1000000000) ≤ -Real.log (5120 / 7117) ∧
    -Real.log (5120 / 7117) ≤ (6586637 / 20000000) := by
  have h := checkLog_sound (w := (1997 / 12237)) (n := 12)
    (lo := (329331849 / 1000000000)) (hi := (6586637 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7117 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7117 / 5120) = 1/(5120 / 7117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (329331849 / 1000000000) (6586637 / 20000000) (Real.log (7117 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7117 / 5120) = -Real.log (5120 / 7117) := by
    rw [show ((7117 / 5120) : ℝ) = ((5120 / 7117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (12359009 / 25000000) ≤ -Real.log (3123 / 5120) ∧
    -Real.log (3123 / 5120) ≤ (494360361 / 1000000000) := by
  have h := checkLog_sound (w := (1997 / 8243)) (n := 12)
    (lo := (12359009 / 25000000)) (hi := (494360361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3123) = 1/(3123 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-494360361 / 1000000000) (-12359009 / 25000000) (Real.log (3123 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122517879 / 500000000) ≤ -Real.log (1000000 / 1277667) ∧
    -Real.log (1000000 / 1277667) ≤ (245035759 / 1000000000) := by
  have h := checkLog_sound (w := (277667 / 2277667)) (n := 12)
    (lo := (122517879 / 500000000)) (hi := (245035759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277667 / 1000000) = 1/(1000000 / 1277667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122517879 / 500000000) (245035759 / 1000000000) (Real.log (1277667 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1277667 / 1000000) = -Real.log (1000000 / 1277667) := by
    rw [show ((1277667 / 1000000) : ℝ) = ((1000000 / 1277667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325269027 / 1000000000) ≤ -Real.log (722333 / 1000000) ∧
    -Real.log (722333 / 1000000) ≤ (81317257 / 250000000) := by
  have h := checkLog_sound (w := (277667 / 1722333)) (n := 12)
    (lo := (325269027 / 1000000000)) (hi := (81317257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 722333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 722333) = 1/(722333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-81317257 / 250000000) (-325269027 / 1000000000) (Real.log (722333 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122683779 / 500000000) ≤ -Real.log (1000000 / 1278091) ∧
    -Real.log (1000000 / 1278091) ≤ (245367559 / 1000000000) := by
  have h := checkLog_sound (w := (278091 / 2278091)) (n := 12)
    (lo := (122683779 / 500000000)) (hi := (245367559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278091 / 1000000) = 1/(1000000 / 1278091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122683779 / 500000000) (245367559 / 1000000000) (Real.log (1278091 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1278091 / 1000000) = -Real.log (1000000 / 1278091) := by
    rw [show ((1278091 / 1000000) : ℝ) = ((1000000 / 1278091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (162928093 / 500000000) ≤ -Real.log (721909 / 1000000) ∧
    -Real.log (721909 / 1000000) ≤ (325856187 / 1000000000) := by
  have h := checkLog_sound (w := (278091 / 1721909)) (n := 12)
    (lo := (162928093 / 500000000)) (hi := (325856187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721909) = 1/(721909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-325856187 / 1000000000) (-162928093 / 500000000) (Real.log (721909 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (182841421 / 1000000000) ≤ -Real.log (62500 / 75039) ∧
    -Real.log (62500 / 75039) ≤ (91420711 / 500000000) := by
  have h := checkLog_sound (w := (12539 / 137539)) (n := 12)
    (lo := (182841421 / 1000000000)) (hi := (91420711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75039 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75039 / 62500) = 1/(62500 / 75039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (182841421 / 1000000000) (91420711 / 500000000) (Real.log (75039 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (75039 / 62500) = -Real.log (62500 / 75039) := by
    rw [show ((75039 / 62500) : ℝ) = ((62500 / 75039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (44784771 / 200000000) ≤ -Real.log (49961 / 62500) ∧
    -Real.log (49961 / 62500) ≤ (13995241 / 62500000) := by
  have h := checkLog_sound (w := (12539 / 112461)) (n := 12)
    (lo := (44784771 / 200000000)) (hi := (13995241 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49961) = 1/(49961 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13995241 / 62500000) (-44784771 / 200000000) (Real.log (49961 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91553957 / 500000000) ≤ -Real.log (62500 / 75059) ∧
    -Real.log (62500 / 75059) ≤ (36621583 / 200000000) := by
  have h := checkLog_sound (w := (12559 / 137559)) (n := 12)
    (lo := (91553957 / 500000000)) (hi := (36621583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75059 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75059 / 62500) = 1/(62500 / 75059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91553957 / 500000000) (36621583 / 200000000) (Real.log (75059 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (75059 / 62500) = -Real.log (62500 / 75059) := by
    rw [show ((75059 / 62500) : ℝ) = ((62500 / 75059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28040531 / 125000000) ≤ -Real.log (49941 / 62500) ∧
    -Real.log (49941 / 62500) ≤ (224324249 / 1000000000) := by
  have h := checkLog_sound (w := (12559 / 112441)) (n := 12)
    (lo := (28040531 / 125000000)) (hi := (224324249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49941) = 1/(49941 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224324249 / 1000000000) (-28040531 / 125000000) (Real.log (49941 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (823692209 / 1000000000) ≤ -Real.log (250000000000 / 569724623759) ∧
    -Real.log (250000000000 / 569724623759) ≤ (823692211 / 1000000000) := by
  have h := checkLog_sound (w := (69724623759 / 1069724623759)) (n := 12)
    (lo := (130545029 / 1000000000)) (hi := (13054503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569724623759 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(569724623759 / 500000000000) = 1/(250000000000 / 569724623759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (823692209 / 1000000000) (823692211 / 1000000000) (Real.log (569724623759 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (569724623759 / 250000000000) = -Real.log (250000000000 / 569724623759) := by
    rw [show ((569724623759 / 250000000000) : ℝ) = ((250000000000 / 569724623759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (825074723 / 1000000000) ≤ -Real.log (250000000000 / 570512820513) ∧
    -Real.log (250000000000 / 570512820513) ≤ (33002989 / 40000000) := by
  have h := checkLog_sound (w := (70512820513 / 1070512820513)) (n := 12)
    (lo := (131927543 / 1000000000)) (hi := (16490943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570512820513 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(570512820513 / 500000000000) = 1/(250000000000 / 570512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (825074723 / 1000000000) (33002989 / 40000000) (Real.log (570512820513 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (570512820513 / 250000000000) = -Real.log (250000000000 / 570512820513) := by
    rw [show ((570512820513 / 250000000000) : ℝ) = ((250000000000 / 570512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (285152393 / 500000000) ≤ -Real.log (500000000000 / 884403038487) ∧
    -Real.log (500000000000 / 884403038487) ≤ (570304787 / 1000000000) := by
  have h := checkLog_sound (w := (384403038487 / 1384403038487)) (n := 12)
    (lo := (285152393 / 500000000)) (hi := (570304787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884403038487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884403038487 / 500000000000) = 1/(500000000000 / 884403038487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (285152393 / 500000000) (570304787 / 1000000000) (Real.log (884403038487 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (884403038487 / 500000000000) = -Real.log (500000000000 / 884403038487) := by
    rw [show ((884403038487 / 500000000000) : ℝ) = ((500000000000 / 884403038487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (114244749 / 200000000) ≤ -Real.log (500000000000 / 885216142201) ∧
    -Real.log (500000000000 / 885216142201) ≤ (285611873 / 500000000) := by
  have h := checkLog_sound (w := (385216142201 / 1385216142201)) (n := 12)
    (lo := (114244749 / 200000000)) (hi := (285611873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885216142201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885216142201 / 500000000000) = 1/(500000000000 / 885216142201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (114244749 / 200000000) (285611873 / 500000000) (Real.log (885216142201 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (885216142201 / 500000000000) = -Real.log (500000000000 / 885216142201) := by
    rw [show ((885216142201 / 500000000000) : ℝ) = ((500000000000 / 885216142201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (406765277 / 1000000000) ≤ -Real.log (500000000000 / 750975761093) ∧
    -Real.log (500000000000 / 750975761093) ≤ (203382639 / 500000000) := by
  have h := checkLog_sound (w := (250975761093 / 1250975761093)) (n := 12)
    (lo := (406765277 / 1000000000)) (hi := (203382639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750975761093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750975761093 / 500000000000) = 1/(500000000000 / 750975761093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (406765277 / 1000000000) (203382639 / 500000000) (Real.log (750975761093 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (750975761093 / 500000000000) = -Real.log (500000000000 / 750975761093) := by
    rw [show ((750975761093 / 500000000000) : ℝ) = ((500000000000 / 750975761093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (203716081 / 500000000) ≤ -Real.log (500000000000 / 751476742557) ∧
    -Real.log (500000000000 / 751476742557) ≤ (407432163 / 1000000000) := by
  have h := checkLog_sound (w := (251476742557 / 1251476742557)) (n := 12)
    (lo := (203716081 / 500000000)) (hi := (407432163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751476742557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751476742557 / 500000000000) = 1/(500000000000 / 751476742557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (203716081 / 500000000) (407432163 / 1000000000) (Real.log (751476742557 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (751476742557 / 500000000000) = -Real.log (500000000000 / 751476742557) := by
    rw [show ((751476742557 / 500000000000) : ℝ) = ((500000000000 / 751476742557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (41216333 / 1000000000) ≤ -Real.log (3748521519 / 3906250000) ∧
    -Real.log (3748521519 / 3906250000) ≤ (20608167 / 500000000) := by
  have h := checkLog_sound (w := (157728481 / 7654771519)) (n := 12)
    (lo := (41216333 / 1000000000)) (hi := (20608167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3748521519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3748521519) = 1/(3748521519 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20608167 / 500000000) (-41216333 / 1000000000) (Real.log (3748521519 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20541217 / 500000000) ≤ -Real.log (3749023479 / 3906250000) ∧
    -Real.log (3749023479 / 3906250000) ≤ (8216487 / 200000000) := by
  have h := checkLog_sound (w := (157226521 / 7655273479)) (n := 12)
    (lo := (20541217 / 500000000)) (hi := (8216487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3749023479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3749023479) = 1/(3749023479 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8216487 / 200000000) (-20541217 / 500000000) (Real.log (3749023479 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell239

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell240Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell240
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

theorem reflection_log_1_neg : (66034909 / 200000000) ≤ -Real.log (5120 / 7123) ∧
    -Real.log (5120 / 7123) ≤ (165087273 / 500000000) := by
  have h := checkLog_sound (w := (2003 / 12243)) (n := 12)
    (lo := (66034909 / 200000000)) (hi := (165087273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7123 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7123 / 5120) = 1/(5120 / 7123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66034909 / 200000000) (165087273 / 500000000) (Real.log (7123 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7123 / 5120) = -Real.log (5120 / 7123) := by
    rw [show ((7123 / 5120) : ℝ) = ((5120 / 7123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (248141719 / 500000000) ≤ -Real.log (3117 / 5120) ∧
    -Real.log (3117 / 5120) ≤ (496283439 / 1000000000) := by
  have h := checkLog_sound (w := (2003 / 8237)) (n := 12)
    (lo := (248141719 / 500000000)) (hi := (496283439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3117) = 1/(3117 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-496283439 / 1000000000) (-248141719 / 500000000) (Real.log (3117 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164876643 / 500000000) ≤ -Real.log (64 / 89) ∧
    -Real.log (64 / 89) ≤ (329753287 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 153)) (n := 12)
    (lo := (164876643 / 500000000)) (hi := (329753287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89 / 64) = 1/(64 / 89) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (164876643 / 500000000) (329753287 / 1000000000) (Real.log (89 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (89 / 64) = -Real.log (64 / 89) := by
    rw [show ((89 / 64) : ℝ) = ((64 / 89) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (495321437 / 1000000000) ≤ -Real.log (39 / 64) ∧
    -Real.log (39 / 64) ≤ (247660719 / 500000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 39) = 1/(39 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-247660719 / 500000000) (-495321437 / 1000000000) (Real.log (39 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30670847 / 125000000) ≤ -Real.log (100000 / 127809) ∧
    -Real.log (100000 / 127809) ≤ (245366777 / 1000000000) := by
  have h := checkLog_sound (w := (27809 / 227809)) (n := 12)
    (lo := (30670847 / 125000000)) (hi := (245366777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127809 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127809 / 100000) = 1/(100000 / 127809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (30670847 / 125000000) (245366777 / 1000000000) (Real.log (127809 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (127809 / 100000) = -Real.log (100000 / 127809) := by
    rw [show ((127809 / 100000) : ℝ) = ((100000 / 127809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325854801 / 1000000000) ≤ -Real.log (72191 / 100000) ∧
    -Real.log (72191 / 100000) ≤ (162927401 / 500000000) := by
  have h := checkLog_sound (w := (27809 / 172191)) (n := 12)
    (lo := (325854801 / 1000000000)) (hi := (162927401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72191) = 1/(72191 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-162927401 / 500000000) (-325854801 / 1000000000) (Real.log (72191 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122849233 / 500000000) ≤ -Real.log (500000 / 639257) ∧
    -Real.log (500000 / 639257) ≤ (245698467 / 1000000000) := by
  have h := checkLog_sound (w := (139257 / 1139257)) (n := 12)
    (lo := (122849233 / 500000000)) (hi := (245698467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639257 / 500000) = 1/(500000 / 639257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122849233 / 500000000) (245698467 / 1000000000) (Real.log (639257 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (639257 / 500000) = -Real.log (500000 / 639257) := by
    rw [show ((639257 / 500000) : ℝ) = ((500000 / 639257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5100661 / 15625000) ≤ -Real.log (360743 / 500000) ∧
    -Real.log (360743 / 500000) ≤ (65288461 / 200000000) := by
  have h := checkLog_sound (w := (139257 / 860743)) (n := 12)
    (lo := (5100661 / 15625000)) (hi := (65288461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 360743) = 1/(360743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-65288461 / 200000000) (-5100661 / 15625000) (Real.log (360743 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (183107081 / 1000000000) ≤ -Real.log (1000000 / 1200943) ∧
    -Real.log (1000000 / 1200943) ≤ (91553541 / 500000000) := by
  have h := checkLog_sound (w := (200943 / 2200943)) (n := 12)
    (lo := (183107081 / 1000000000)) (hi := (91553541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200943 / 1000000) = 1/(1000000 / 1200943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (183107081 / 1000000000) (91553541 / 500000000) (Real.log (1200943 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1200943 / 1000000) = -Real.log (1000000 / 1200943) := by
    rw [show ((1200943 / 1000000) : ℝ) = ((1000000 / 1200943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (56080749 / 250000000) ≤ -Real.log (799057 / 1000000) ∧
    -Real.log (799057 / 1000000) ≤ (224322997 / 1000000000) := by
  have h := checkLog_sound (w := (200943 / 1799057)) (n := 12)
    (lo := (56080749 / 250000000)) (hi := (224322997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799057) = 1/(799057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-224322997 / 1000000000) (-56080749 / 250000000) (Real.log (799057 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (183373503 / 1000000000) ≤ -Real.log (1000000 / 1201263) ∧
    -Real.log (1000000 / 1201263) ≤ (2865211 / 15625000) := by
  have h := checkLog_sound (w := (201263 / 2201263)) (n := 12)
    (lo := (183373503 / 1000000000)) (hi := (2865211 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201263 / 1000000) = 1/(1000000 / 1201263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (183373503 / 1000000000) (2865211 / 15625000) (Real.log (1201263 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1201263 / 1000000) = -Real.log (1000000 / 1201263) := by
    rw [show ((1201263 / 1000000) : ℝ) = ((1000000 / 1201263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56180887 / 250000000) ≤ -Real.log (798737 / 1000000) ∧
    -Real.log (798737 / 1000000) ≤ (224723549 / 1000000000) := by
  have h := checkLog_sound (w := (201263 / 1798737)) (n := 12)
    (lo := (56180887 / 250000000)) (hi := (224723549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798737) = 1/(798737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224723549 / 1000000000) (-56180887 / 250000000) (Real.log (798737 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (825074723 / 1000000000) ≤ -Real.log (20000000000 / 45641025641) ∧
    -Real.log (20000000000 / 45641025641) ≤ (33002989 / 40000000) := by
  have h := checkLog_sound (w := (5641025641 / 85641025641)) (n := 12)
    (lo := (131927543 / 1000000000)) (hi := (16490943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45641025641 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(45641025641 / 40000000000) = 1/(20000000000 / 45641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (825074723 / 1000000000) (33002989 / 40000000) (Real.log (45641025641 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (45641025641 / 20000000000) = -Real.log (20000000000 / 45641025641) := by
    rw [show ((45641025641 / 20000000000) : ℝ) = ((20000000000 / 45641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (826457983 / 1000000000) ≤ -Real.log (500000000000 / 1142605068977) ∧
    -Real.log (500000000000 / 1142605068977) ≤ (165291597 / 200000000) := by
  have h := checkLog_sound (w := (142605068977 / 2142605068977)) (n := 12)
    (lo := (133310803 / 1000000000)) (hi := (33327701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142605068977 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1142605068977 / 1000000000000) = 1/(500000000000 / 1142605068977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (826457983 / 1000000000) (165291597 / 200000000) (Real.log (1142605068977 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1142605068977 / 500000000000) = -Real.log (500000000000 / 1142605068977) := by
    rw [show ((1142605068977 / 500000000000) : ℝ) = ((500000000000 / 1142605068977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (571221577 / 1000000000) ≤ -Real.log (500000000000 / 885214223379) ∧
    -Real.log (500000000000 / 885214223379) ≤ (285610789 / 500000000) := by
  have h := checkLog_sound (w := (385214223379 / 1385214223379)) (n := 12)
    (lo := (571221577 / 1000000000)) (hi := (285610789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885214223379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885214223379 / 500000000000) = 1/(500000000000 / 885214223379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (571221577 / 1000000000) (285610789 / 500000000) (Real.log (885214223379 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (885214223379 / 500000000000) = -Real.log (500000000000 / 885214223379) := by
    rw [show ((885214223379 / 500000000000) : ℝ) = ((500000000000 / 885214223379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57214077 / 100000000) ≤ -Real.log (250000000000 / 443014140261) ∧
    -Real.log (250000000000 / 443014140261) ≤ (572140771 / 1000000000) := by
  have h := checkLog_sound (w := (193014140261 / 693014140261)) (n := 12)
    (lo := (57214077 / 100000000)) (hi := (572140771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443014140261 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443014140261 / 250000000000) = 1/(250000000000 / 443014140261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (57214077 / 100000000) (572140771 / 1000000000) (Real.log (443014140261 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (443014140261 / 250000000000) = -Real.log (250000000000 / 443014140261) := by
    rw [show ((443014140261 / 250000000000) : ℝ) = ((250000000000 / 443014140261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (203715039 / 500000000) ≤ -Real.log (125000000000 / 187868794091) ∧
    -Real.log (125000000000 / 187868794091) ≤ (407430079 / 1000000000) := by
  have h := checkLog_sound (w := (62868794091 / 312868794091)) (n := 12)
    (lo := (203715039 / 500000000)) (hi := (407430079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187868794091 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187868794091 / 125000000000) = 1/(125000000000 / 187868794091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (203715039 / 500000000) (407430079 / 1000000000) (Real.log (187868794091 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (187868794091 / 125000000000) = -Real.log (125000000000 / 187868794091) := by
    rw [show ((187868794091 / 125000000000) : ℝ) = ((125000000000 / 187868794091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (102024263 / 250000000) ≤ -Real.log (500000000000 / 751976557991) ∧
    -Real.log (500000000000 / 751976557991) ≤ (408097053 / 1000000000) := by
  have h := checkLog_sound (w := (251976557991 / 1251976557991)) (n := 12)
    (lo := (102024263 / 250000000)) (hi := (408097053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751976557991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751976557991 / 500000000000) = 1/(500000000000 / 751976557991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (102024263 / 250000000) (408097053 / 1000000000) (Real.log (751976557991 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (751976557991 / 500000000000) = -Real.log (500000000000 / 751976557991) := by
    rw [show ((751976557991 / 500000000000) : ℝ) = ((500000000000 / 751976557991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8270009 / 200000000) ≤ -Real.log (959493204831 / 1000000000000) ∧
    -Real.log (959493204831 / 1000000000000) ≤ (20675023 / 500000000) := by
  have h := checkLog_sound (w := (40506795169 / 1959493204831)) (n := 12)
    (lo := (8270009 / 200000000)) (hi := (20675023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959493204831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959493204831) = 1/(959493204831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20675023 / 500000000) (-8270009 / 200000000) (Real.log (959493204831 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8243183 / 200000000) ≤ -Real.log (959621910751 / 1000000000000) ∧
    -Real.log (959621910751 / 1000000000000) ≤ (10303979 / 250000000) := by
  have h := checkLog_sound (w := (40378089249 / 1959621910751)) (n := 12)
    (lo := (8243183 / 200000000)) (hi := (10303979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959621910751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959621910751) = 1/(959621910751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10303979 / 250000000) (-8243183 / 200000000) (Real.log (959621910751 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell240

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell241Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell241
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

theorem reflection_log_1_neg : (82648907 / 250000000) ≤ -Real.log (2560 / 3563) ∧
    -Real.log (2560 / 3563) ≤ (330595629 / 1000000000) := by
  have h := checkLog_sound (w := (1003 / 6123)) (n := 12)
    (lo := (82648907 / 250000000)) (hi := (330595629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3563 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3563 / 2560) = 1/(2560 / 3563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (82648907 / 250000000) (330595629 / 1000000000) (Real.log (3563 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3563 / 2560) = -Real.log (2560 / 3563) := by
    rw [show ((3563 / 2560) : ℝ) = ((2560 / 3563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99449273 / 200000000) ≤ -Real.log (1557 / 2560) ∧
    -Real.log (1557 / 2560) ≤ (248623183 / 500000000) := by
  have h := checkLog_sound (w := (1003 / 4117)) (n := 12)
    (lo := (99449273 / 200000000)) (hi := (248623183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1557) = 1/(1557 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-248623183 / 500000000) (-99449273 / 200000000) (Real.log (1557 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66034909 / 200000000) ≤ -Real.log (5120 / 7123) ∧
    -Real.log (5120 / 7123) ≤ (165087273 / 500000000) := by
  have h := checkLog_sound (w := (2003 / 12243)) (n := 12)
    (lo := (66034909 / 200000000)) (hi := (165087273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7123 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7123 / 5120) = 1/(5120 / 7123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66034909 / 200000000) (165087273 / 500000000) (Real.log (7123 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7123 / 5120) = -Real.log (5120 / 7123) := by
    rw [show ((7123 / 5120) : ℝ) = ((5120 / 7123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (248141719 / 500000000) ≤ -Real.log (3117 / 5120) ∧
    -Real.log (3117 / 5120) ≤ (496283439 / 1000000000) := by
  have h := checkLog_sound (w := (2003 / 8237)) (n := 12)
    (lo := (248141719 / 500000000)) (hi := (496283439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3117) = 1/(3117 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-496283439 / 1000000000) (-248141719 / 500000000) (Real.log (3117 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (245697683 / 1000000000) ≤ -Real.log (1000000 / 1278513) ∧
    -Real.log (1000000 / 1278513) ≤ (61424421 / 250000000) := by
  have h := checkLog_sound (w := (278513 / 2278513)) (n := 12)
    (lo := (245697683 / 1000000000)) (hi := (61424421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278513 / 1000000) = 1/(1000000 / 1278513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (245697683 / 1000000000) (61424421 / 250000000) (Real.log (1278513 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1278513 / 1000000) = -Real.log (1000000 / 1278513) := by
    rw [show ((1278513 / 1000000) : ℝ) = ((1000000 / 1278513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (163220459 / 500000000) ≤ -Real.log (721487 / 1000000) ∧
    -Real.log (721487 / 1000000) ≤ (326440919 / 1000000000) := by
  have h := checkLog_sound (w := (278513 / 1721487)) (n := 12)
    (lo := (163220459 / 500000000)) (hi := (326440919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721487) = 1/(721487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-326440919 / 1000000000) (-163220459 / 500000000) (Real.log (721487 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (123015023 / 500000000) ≤ -Real.log (500000 / 639469) ∧
    -Real.log (500000 / 639469) ≤ (246030047 / 1000000000) := by
  have h := checkLog_sound (w := (139469 / 1139469)) (n := 12)
    (lo := (123015023 / 500000000)) (hi := (246030047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639469 / 500000) = 1/(500000 / 639469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (123015023 / 500000000) (246030047 / 1000000000) (Real.log (639469 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (639469 / 500000) = -Real.log (500000 / 639469) := by
    rw [show ((639469 / 500000) : ℝ) = ((500000 / 639469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (327030153 / 1000000000) ≤ -Real.log (360531 / 500000) ∧
    -Real.log (360531 / 500000) ≤ (163515077 / 500000000) := by
  have h := checkLog_sound (w := (139469 / 860531)) (n := 12)
    (lo := (327030153 / 1000000000)) (hi := (163515077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 360531) = 1/(360531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-163515077 / 500000000) (-327030153 / 1000000000) (Real.log (360531 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18337267 / 100000000) ≤ -Real.log (500000 / 600631) ∧
    -Real.log (500000 / 600631) ≤ (183372671 / 1000000000) := by
  have h := checkLog_sound (w := (100631 / 1100631)) (n := 12)
    (lo := (18337267 / 100000000)) (hi := (183372671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600631 / 500000) = 1/(500000 / 600631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18337267 / 100000000) (183372671 / 1000000000) (Real.log (600631 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (600631 / 500000) = -Real.log (500000 / 600631) := by
    rw [show ((600631 / 500000) : ℝ) = ((500000 / 600631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (28090287 / 125000000) ≤ -Real.log (399369 / 500000) ∧
    -Real.log (399369 / 500000) ≤ (224722297 / 1000000000) := by
  have h := checkLog_sound (w := (100631 / 899369)) (n := 12)
    (lo := (28090287 / 125000000)) (hi := (224722297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399369) = 1/(399369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-224722297 / 1000000000) (-28090287 / 125000000) (Real.log (399369 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (183639021 / 1000000000) ≤ -Real.log (500000 / 600791) ∧
    -Real.log (500000 / 600791) ≤ (91819511 / 500000000) := by
  have h := checkLog_sound (w := (100791 / 1100791)) (n := 12)
    (lo := (183639021 / 1000000000)) (hi := (91819511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600791 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600791 / 500000) = 1/(500000 / 600791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (183639021 / 1000000000) (91819511 / 500000000) (Real.log (600791 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (600791 / 500000) = -Real.log (500000 / 600791) := by
    rw [show ((600791 / 500000) : ℝ) = ((500000 / 600791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (225123009 / 1000000000) ≤ -Real.log (399209 / 500000) ∧
    -Real.log (399209 / 500000) ≤ (22512301 / 100000000) := by
  have h := checkLog_sound (w := (100791 / 899209)) (n := 12)
    (lo := (225123009 / 1000000000)) (hi := (22512301 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399209) = 1/(399209 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22512301 / 100000000) (-225123009 / 1000000000) (Real.log (399209 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (826457983 / 1000000000) ≤ -Real.log (31250000000 / 71412816811) ∧
    -Real.log (31250000000 / 71412816811) ≤ (165291597 / 200000000) := by
  have h := checkLog_sound (w := (8912816811 / 133912816811)) (n := 12)
    (lo := (133310803 / 1000000000)) (hi := (33327701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71412816811 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(71412816811 / 62500000000) = 1/(31250000000 / 71412816811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (826457983 / 1000000000) (165291597 / 200000000) (Real.log (71412816811 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (71412816811 / 31250000000) = -Real.log (31250000000 / 71412816811) := by
    rw [show ((71412816811 / 31250000000) : ℝ) = ((31250000000 / 71412816811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (827841993 / 1000000000) ≤ -Real.log (250000000000 / 572093770071) ∧
    -Real.log (250000000000 / 572093770071) ≤ (165568399 / 200000000) := by
  have h := checkLog_sound (w := (72093770071 / 1072093770071)) (n := 12)
    (lo := (134694813 / 1000000000)) (hi := (67347407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572093770071 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572093770071 / 500000000000) = 1/(250000000000 / 572093770071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (827841993 / 1000000000) (165568399 / 200000000) (Real.log (572093770071 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (572093770071 / 250000000000) = -Real.log (250000000000 / 572093770071) := by
    rw [show ((572093770071 / 250000000000) : ℝ) = ((250000000000 / 572093770071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (286069301 / 500000000) ≤ -Real.log (500000000000 / 886026359449) ∧
    -Real.log (500000000000 / 886026359449) ≤ (572138603 / 1000000000) := by
  have h := checkLog_sound (w := (386026359449 / 1386026359449)) (n := 12)
    (lo := (286069301 / 500000000)) (hi := (572138603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886026359449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886026359449 / 500000000000) = 1/(500000000000 / 886026359449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (286069301 / 500000000) (572138603 / 1000000000) (Real.log (886026359449 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (886026359449 / 500000000000) = -Real.log (500000000000 / 886026359449) := by
    rw [show ((886026359449 / 500000000000) : ℝ) = ((500000000000 / 886026359449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (573060199 / 1000000000) ≤ -Real.log (500000000000 / 886843295029) ∧
    -Real.log (500000000000 / 886843295029) ≤ (2865301 / 5000000) := by
  have h := checkLog_sound (w := (386843295029 / 1386843295029)) (n := 12)
    (lo := (573060199 / 1000000000)) (hi := (2865301 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886843295029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886843295029 / 500000000000) = 1/(500000000000 / 886843295029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (573060199 / 1000000000) (2865301 / 5000000) (Real.log (886843295029 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (886843295029 / 500000000000) = -Real.log (500000000000 / 886843295029) := by
    rw [show ((886843295029 / 500000000000) : ℝ) = ((500000000000 / 886843295029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (408094967 / 1000000000) ≤ -Real.log (500000000000 / 751974990547) ∧
    -Real.log (500000000000 / 751974990547) ≤ (51011871 / 125000000) := by
  have h := checkLog_sound (w := (251974990547 / 1251974990547)) (n := 12)
    (lo := (408094967 / 1000000000)) (hi := (51011871 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751974990547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751974990547 / 500000000000) = 1/(500000000000 / 751974990547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (408094967 / 1000000000) (51011871 / 125000000) (Real.log (751974990547 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (751974990547 / 500000000000) = -Real.log (500000000000 / 751974990547) := by
    rw [show ((751974990547 / 500000000000) : ℝ) = ((500000000000 / 751974990547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (408762031 / 1000000000) ≤ -Real.log (500000000000 / 752476772819) ∧
    -Real.log (500000000000 / 752476772819) ≤ (25547627 / 62500000) := by
  have h := checkLog_sound (w := (252476772819 / 1252476772819)) (n := 12)
    (lo := (408762031 / 1000000000)) (hi := (25547627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752476772819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752476772819 / 500000000000) = 1/(500000000000 / 752476772819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (408762031 / 1000000000) (25547627 / 62500000) (Real.log (752476772819 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (752476772819 / 500000000000) = -Real.log (500000000000 / 752476772819) := by
    rw [show ((752476772819 / 500000000000) : ℝ) = ((500000000000 / 752476772819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (41483987 / 1000000000) ≤ -Real.log (239841174319 / 250000000000) ∧
    -Real.log (239841174319 / 250000000000) ≤ (10370997 / 250000000) := by
  have h := checkLog_sound (w := (10158825681 / 489841174319)) (n := 12)
    (lo := (41483987 / 1000000000)) (hi := (10370997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239841174319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239841174319) = 1/(239841174319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-10370997 / 250000000) (-41483987 / 1000000000) (Real.log (239841174319 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20674813 / 500000000) ≤ -Real.log (239873401839 / 250000000000) ∧
    -Real.log (239873401839 / 250000000000) ≤ (41349627 / 1000000000) := by
  have h := checkLog_sound (w := (10126598161 / 489873401839)) (n := 12)
    (lo := (20674813 / 500000000)) (hi := (41349627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239873401839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239873401839) = 1/(239873401839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-41349627 / 1000000000) (-20674813 / 500000000) (Real.log (239873401839 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell241

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell242Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell242
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

theorem reflection_log_1_neg : (331016533 / 1000000000) ≤ -Real.log (5120 / 7129) ∧
    -Real.log (5120 / 7129) ≤ (165508267 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 12249)) (n := 12)
    (lo := (331016533 / 1000000000)) (hi := (165508267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7129 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7129 / 5120) = 1/(5120 / 7129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331016533 / 1000000000) (165508267 / 500000000) (Real.log (7129 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7129 / 5120) = -Real.log (5120 / 7129) := by
    rw [show ((7129 / 5120) : ℝ) = ((5120 / 7129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (498210221 / 1000000000) ≤ -Real.log (3111 / 5120) ∧
    -Real.log (3111 / 5120) ≤ (249105111 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 8231)) (n := 12)
    (lo := (498210221 / 1000000000)) (hi := (249105111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3111) = 1/(3111 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-249105111 / 500000000) (-498210221 / 1000000000) (Real.log (3111 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (82648907 / 250000000) ≤ -Real.log (2560 / 3563) ∧
    -Real.log (2560 / 3563) ≤ (330595629 / 1000000000) := by
  have h := checkLog_sound (w := (1003 / 6123)) (n := 12)
    (lo := (82648907 / 250000000)) (hi := (330595629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3563 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3563 / 2560) = 1/(2560 / 3563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (82648907 / 250000000) (330595629 / 1000000000) (Real.log (3563 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3563 / 2560) = -Real.log (2560 / 3563) := by
    rw [show ((3563 / 2560) : ℝ) = ((2560 / 3563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99449273 / 200000000) ≤ -Real.log (1557 / 2560) ∧
    -Real.log (1557 / 2560) ≤ (248623183 / 500000000) := by
  have h := checkLog_sound (w := (1003 / 4117)) (n := 12)
    (lo := (99449273 / 200000000)) (hi := (248623183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1557) = 1/(1557 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-248623183 / 500000000) (-99449273 / 200000000) (Real.log (1557 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (123014241 / 500000000) ≤ -Real.log (125000 / 159867) ∧
    -Real.log (125000 / 159867) ≤ (246028483 / 1000000000) := by
  have h := checkLog_sound (w := (34867 / 284867)) (n := 12)
    (lo := (123014241 / 500000000)) (hi := (246028483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159867 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159867 / 125000) = 1/(125000 / 159867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (123014241 / 500000000) (246028483 / 1000000000) (Real.log (159867 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (159867 / 125000) = -Real.log (125000 / 159867) := by
    rw [show ((159867 / 125000) : ℝ) = ((125000 / 159867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (16351369 / 50000000) ≤ -Real.log (90133 / 125000) ∧
    -Real.log (90133 / 125000) ≤ (327027381 / 1000000000) := by
  have h := checkLog_sound (w := (34867 / 215133)) (n := 12)
    (lo := (16351369 / 50000000)) (hi := (327027381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90133) = 1/(90133 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-327027381 / 1000000000) (-16351369 / 50000000) (Real.log (90133 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (123180367 / 500000000) ≤ -Real.log (1000000 / 1279361) ∧
    -Real.log (1000000 / 1279361) ≤ (49272147 / 200000000) := by
  have h := checkLog_sound (w := (279361 / 2279361)) (n := 12)
    (lo := (123180367 / 500000000)) (hi := (49272147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279361 / 1000000) = 1/(1000000 / 1279361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (123180367 / 500000000) (49272147 / 200000000) (Real.log (1279361 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1279361 / 1000000) = -Real.log (1000000 / 1279361) := by
    rw [show ((1279361 / 1000000) : ℝ) = ((1000000 / 1279361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1023803 / 3125000) ≤ -Real.log (720639 / 1000000) ∧
    -Real.log (720639 / 1000000) ≤ (327616961 / 1000000000) := by
  have h := checkLog_sound (w := (279361 / 1720639)) (n := 12)
    (lo := (1023803 / 3125000)) (hi := (327616961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720639) = 1/(720639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-327616961 / 1000000000) (-1023803 / 3125000) (Real.log (720639 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (183638189 / 1000000000) ≤ -Real.log (1000000 / 1201581) ∧
    -Real.log (1000000 / 1201581) ≤ (18363819 / 100000000) := by
  have h := checkLog_sound (w := (201581 / 2201581)) (n := 12)
    (lo := (183638189 / 1000000000)) (hi := (18363819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201581 / 1000000) = 1/(1000000 / 1201581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (183638189 / 1000000000) (18363819 / 100000000) (Real.log (1201581 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1201581 / 1000000) = -Real.log (1000000 / 1201581) := by
    rw [show ((1201581 / 1000000) : ℝ) = ((1000000 / 1201581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (56280439 / 250000000) ≤ -Real.log (798419 / 1000000) ∧
    -Real.log (798419 / 1000000) ≤ (225121757 / 1000000000) := by
  have h := checkLog_sound (w := (201581 / 1798419)) (n := 12)
    (lo := (56280439 / 250000000)) (hi := (225121757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798419) = 1/(798419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225121757 / 1000000000) (-56280439 / 250000000) (Real.log (798419 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91952651 / 500000000) ≤ -Real.log (500000 / 600951) ∧
    -Real.log (500000 / 600951) ≤ (183905303 / 1000000000) := by
  have h := checkLog_sound (w := (100951 / 1100951)) (n := 12)
    (lo := (91952651 / 500000000)) (hi := (183905303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600951 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600951 / 500000) = 1/(500000 / 600951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91952651 / 500000000) (183905303 / 1000000000) (Real.log (600951 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (600951 / 500000) = -Real.log (500000 / 600951) := by
    rw [show ((600951 / 500000) : ℝ) = ((500000 / 600951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112761941 / 500000000) ≤ -Real.log (399049 / 500000) ∧
    -Real.log (399049 / 500000) ≤ (225523883 / 1000000000) := by
  have h := checkLog_sound (w := (100951 / 899049)) (n := 12)
    (lo := (112761941 / 500000000)) (hi := (225523883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399049) = 1/(399049 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-225523883 / 1000000000) (-112761941 / 500000000) (Real.log (399049 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (827841993 / 1000000000) ≤ -Real.log (500000000000 / 1144187540141) ∧
    -Real.log (500000000000 / 1144187540141) ≤ (165568399 / 200000000) := by
  have h := checkLog_sound (w := (144187540141 / 2144187540141)) (n := 12)
    (lo := (134694813 / 1000000000)) (hi := (67347407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144187540141 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1144187540141 / 1000000000000) = 1/(500000000000 / 1144187540141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (827841993 / 1000000000) (165568399 / 200000000) (Real.log (1144187540141 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1144187540141 / 500000000000) = -Real.log (500000000000 / 1144187540141) := by
    rw [show ((1144187540141 / 500000000000) : ℝ) = ((500000000000 / 1144187540141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (829226753 / 1000000000) ≤ -Real.log (125000000000 / 286443265831) ∧
    -Real.log (125000000000 / 286443265831) ≤ (165845351 / 200000000) := by
  have h := checkLog_sound (w := (36443265831 / 536443265831)) (n := 12)
    (lo := (136079573 / 1000000000)) (hi := (68039787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286443265831 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(286443265831 / 250000000000) = 1/(125000000000 / 286443265831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (829226753 / 1000000000) (165845351 / 200000000) (Real.log (286443265831 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (286443265831 / 125000000000) = -Real.log (125000000000 / 286443265831) := by
    rw [show ((286443265831 / 125000000000) : ℝ) = ((125000000000 / 286443265831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (286527931 / 500000000) ≤ -Real.log (50000000000 / 88683944837) ∧
    -Real.log (50000000000 / 88683944837) ≤ (573055863 / 1000000000) := by
  have h := checkLog_sound (w := (38683944837 / 138683944837)) (n := 12)
    (lo := (286527931 / 500000000)) (hi := (573055863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88683944837 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88683944837 / 50000000000) = 1/(50000000000 / 88683944837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (286527931 / 500000000) (573055863 / 1000000000) (Real.log (88683944837 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (88683944837 / 50000000000) = -Real.log (50000000000 / 88683944837) := by
    rw [show ((88683944837 / 50000000000) : ℝ) = ((50000000000 / 88683944837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (114795539 / 200000000) ≤ -Real.log (500000000000 / 887657342997) ∧
    -Real.log (500000000000 / 887657342997) ≤ (17936803 / 31250000) := by
  have h := checkLog_sound (w := (387657342997 / 1387657342997)) (n := 12)
    (lo := (114795539 / 200000000)) (hi := (17936803 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887657342997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887657342997 / 500000000000) = 1/(500000000000 / 887657342997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (114795539 / 200000000) (17936803 / 31250000) (Real.log (887657342997 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (887657342997 / 500000000000) = -Real.log (500000000000 / 887657342997) := by
    rw [show ((887657342997 / 500000000000) : ℝ) = ((500000000000 / 887657342997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (204379973 / 500000000) ≤ -Real.log (250000000000 / 376237602061) ∧
    -Real.log (250000000000 / 376237602061) ≤ (408759947 / 1000000000) := by
  have h := checkLog_sound (w := (126237602061 / 626237602061)) (n := 12)
    (lo := (204379973 / 500000000)) (hi := (408759947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376237602061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376237602061 / 250000000000) = 1/(250000000000 / 376237602061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (204379973 / 500000000) (408759947 / 1000000000) (Real.log (376237602061 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (376237602061 / 250000000000) = -Real.log (250000000000 / 376237602061) := by
    rw [show ((376237602061 / 250000000000) : ℝ) = ((250000000000 / 376237602061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (6397331 / 15625000) ≤ -Real.log (15625000000 / 23530592421) ∧
    -Real.log (15625000000 / 23530592421) ≤ (81885837 / 200000000) := by
  have h := checkLog_sound (w := (7905592421 / 39155592421)) (n := 12)
    (lo := (6397331 / 15625000)) (hi := (81885837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23530592421 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23530592421 / 15625000000) = 1/(15625000000 / 23530592421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (6397331 / 15625000) (81885837 / 200000000) (Real.log (23530592421 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23530592421 / 15625000000) = -Real.log (15625000000 / 23530592421) := by
    rw [show ((23530592421 / 15625000000) : ℝ) = ((15625000000 / 23530592421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2080929 / 50000000) ≤ -Real.log (239808895599 / 250000000000) ∧
    -Real.log (239808895599 / 250000000000) ≤ (41618581 / 1000000000) := by
  have h := checkLog_sound (w := (10191104401 / 489808895599)) (n := 12)
    (lo := (2080929 / 50000000)) (hi := (41618581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239808895599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239808895599) = 1/(239808895599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41618581 / 1000000000) (-2080929 / 50000000) (Real.log (239808895599 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (41483567 / 1000000000) ≤ -Real.log (959365100439 / 1000000000000) ∧
    -Real.log (959365100439 / 1000000000000) ≤ (2592723 / 62500000) := by
  have h := checkLog_sound (w := (40634899561 / 1959365100439)) (n := 12)
    (lo := (41483567 / 1000000000)) (hi := (2592723 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959365100439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959365100439) = 1/(959365100439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2592723 / 62500000) (-41483567 / 1000000000) (Real.log (959365100439 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell242

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell243Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell243
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

theorem reflection_log_1_neg : (16571863 / 50000000) ≤ -Real.log (1280 / 1783) ∧
    -Real.log (1280 / 1783) ≤ (331437261 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 3063)) (n := 12)
    (lo := (16571863 / 50000000)) (hi := (331437261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1783 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1783 / 1280) = 1/(1280 / 1783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16571863 / 50000000) (331437261 / 1000000000) (Real.log (1783 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1783 / 1280) = -Real.log (1280 / 1783) := by
    rw [show ((1783 / 1280) : ℝ) = ((1280 / 1783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249587503 / 500000000) ≤ -Real.log (777 / 1280) ∧
    -Real.log (777 / 1280) ≤ (499175007 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2057)) (n := 12)
    (lo := (249587503 / 500000000)) (hi := (499175007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 777) = 1/(777 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-499175007 / 1000000000) (-249587503 / 500000000) (Real.log (777 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331016533 / 1000000000) ≤ -Real.log (5120 / 7129) ∧
    -Real.log (5120 / 7129) ≤ (165508267 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 12249)) (n := 12)
    (lo := (331016533 / 1000000000)) (hi := (165508267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7129 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7129 / 5120) = 1/(5120 / 7129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331016533 / 1000000000) (165508267 / 500000000) (Real.log (7129 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7129 / 5120) = -Real.log (5120 / 7129) := by
    rw [show ((7129 / 5120) : ℝ) = ((5120 / 7129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (498210221 / 1000000000) ≤ -Real.log (3111 / 5120) ∧
    -Real.log (3111 / 5120) ≤ (249105111 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 8231)) (n := 12)
    (lo := (498210221 / 1000000000)) (hi := (249105111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3111) = 1/(3111 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-249105111 / 500000000) (-498210221 / 1000000000) (Real.log (3111 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15397497 / 62500000) ≤ -Real.log (3125 / 3998) ∧
    -Real.log (3125 / 3998) ≤ (246359953 / 1000000000) := by
  have h := checkLog_sound (w := (873 / 7123)) (n := 12)
    (lo := (15397497 / 62500000)) (hi := (246359953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3998 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3998 / 3125) = 1/(3125 / 3998) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15397497 / 62500000) (246359953 / 1000000000) (Real.log (3998 / 3125)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3998 / 3125) = -Real.log (3125 / 3998) := by
    rw [show ((3998 / 3125) : ℝ) = ((3125 / 3998) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (81903893 / 250000000) ≤ -Real.log (2252 / 3125) ∧
    -Real.log (2252 / 3125) ≤ (327615573 / 1000000000) := by
  have h := checkLog_sound (w := (873 / 5377)) (n := 12)
    (lo := (81903893 / 250000000)) (hi := (327615573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2252) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2252) = 1/(2252 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-327615573 / 1000000000) (-81903893 / 250000000) (Real.log (2252 / 3125)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (246691313 / 1000000000) ≤ -Real.log (125000 / 159973) ∧
    -Real.log (125000 / 159973) ≤ (123345657 / 500000000) := by
  have h := checkLog_sound (w := (34973 / 284973)) (n := 12)
    (lo := (246691313 / 1000000000)) (hi := (123345657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159973 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159973 / 125000) = 1/(125000 / 159973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (246691313 / 1000000000) (123345657 / 500000000) (Real.log (159973 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (159973 / 125000) = -Real.log (125000 / 159973) := by
    rw [show ((159973 / 125000) : ℝ) = ((125000 / 159973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (328204111 / 1000000000) ≤ -Real.log (90027 / 125000) ∧
    -Real.log (90027 / 125000) ≤ (20512757 / 62500000) := by
  have h := checkLog_sound (w := (34973 / 215027)) (n := 12)
    (lo := (328204111 / 1000000000)) (hi := (20512757 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90027) = 1/(90027 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20512757 / 62500000) (-328204111 / 1000000000) (Real.log (90027 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (183904469 / 1000000000) ≤ -Real.log (1000000 / 1201901) ∧
    -Real.log (1000000 / 1201901) ≤ (18390447 / 100000000) := by
  have h := checkLog_sound (w := (201901 / 2201901)) (n := 12)
    (lo := (183904469 / 1000000000)) (hi := (18390447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201901 / 1000000) = 1/(1000000 / 1201901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (183904469 / 1000000000) (18390447 / 100000000) (Real.log (1201901 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1201901 / 1000000) = -Real.log (1000000 / 1201901) := by
    rw [show ((1201901 / 1000000) : ℝ) = ((1000000 / 1201901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (225522629 / 1000000000) ≤ -Real.log (798099 / 1000000) ∧
    -Real.log (798099 / 1000000) ≤ (22552263 / 100000000) := by
  have h := checkLog_sound (w := (201901 / 1798099)) (n := 12)
    (lo := (225522629 / 1000000000)) (hi := (22552263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798099) = 1/(798099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-22552263 / 100000000) (-225522629 / 1000000000) (Real.log (798099 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (184170679 / 1000000000) ≤ -Real.log (1000000 / 1202221) ∧
    -Real.log (1000000 / 1202221) ≤ (4604267 / 25000000) := by
  have h := checkLog_sound (w := (202221 / 2202221)) (n := 12)
    (lo := (184170679 / 1000000000)) (hi := (4604267 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202221 / 1000000) = 1/(1000000 / 1202221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (184170679 / 1000000000) (4604267 / 25000000) (Real.log (1202221 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1202221 / 1000000) = -Real.log (1000000 / 1202221) := by
    rw [show ((1202221 / 1000000) : ℝ) = ((1000000 / 1202221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112961831 / 500000000) ≤ -Real.log (797779 / 1000000) ∧
    -Real.log (797779 / 1000000) ≤ (225923663 / 1000000000) := by
  have h := checkLog_sound (w := (202221 / 1797779)) (n := 12)
    (lo := (112961831 / 500000000)) (hi := (225923663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797779) = 1/(797779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-225923663 / 1000000000) (-112961831 / 500000000) (Real.log (797779 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (829226753 / 1000000000) ≤ -Real.log (500000000000 / 1145773063323) ∧
    -Real.log (500000000000 / 1145773063323) ≤ (165845351 / 200000000) := by
  have h := checkLog_sound (w := (145773063323 / 2145773063323)) (n := 12)
    (lo := (136079573 / 1000000000)) (hi := (68039787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145773063323 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1145773063323 / 1000000000000) = 1/(500000000000 / 1145773063323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (829226753 / 1000000000) (165845351 / 200000000) (Real.log (1145773063323 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1145773063323 / 500000000000) = -Real.log (500000000000 / 1145773063323) := by
    rw [show ((1145773063323 / 500000000000) : ℝ) = ((500000000000 / 1145773063323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (415306133 / 500000000) ≤ -Real.log (250000000000 / 573680823681) ∧
    -Real.log (250000000000 / 573680823681) ≤ (207653067 / 250000000) := by
  have h := checkLog_sound (w := (73680823681 / 1073680823681)) (n := 12)
    (lo := (68732543 / 500000000)) (hi := (137465087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573680823681 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(573680823681 / 500000000000) = 1/(250000000000 / 573680823681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (415306133 / 500000000) (207653067 / 250000000) (Real.log (573680823681 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (573680823681 / 250000000000) = -Real.log (250000000000 / 573680823681) := by
    rw [show ((573680823681 / 250000000000) : ℝ) = ((250000000000 / 573680823681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22959021 / 40000000) ≤ -Real.log (250000000000 / 443827708703) ∧
    -Real.log (250000000000 / 443827708703) ≤ (286987763 / 500000000) := by
  have h := checkLog_sound (w := (193827708703 / 693827708703)) (n := 12)
    (lo := (22959021 / 40000000)) (hi := (286987763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443827708703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443827708703 / 250000000000) = 1/(250000000000 / 443827708703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22959021 / 40000000) (286987763 / 500000000) (Real.log (443827708703 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (443827708703 / 250000000000) = -Real.log (250000000000 / 443827708703) := by
    rw [show ((443827708703 / 250000000000) : ℝ) = ((250000000000 / 443827708703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (22995817 / 40000000) ≤ -Real.log (100000000000 / 177694469437) ∧
    -Real.log (100000000000 / 177694469437) ≤ (287447713 / 500000000) := by
  have h := checkLog_sound (w := (77694469437 / 277694469437)) (n := 12)
    (lo := (22995817 / 40000000)) (hi := (287447713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177694469437 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177694469437 / 100000000000) = 1/(100000000000 / 177694469437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (22995817 / 40000000) (287447713 / 500000000) (Real.log (177694469437 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (177694469437 / 100000000000) = -Real.log (100000000000 / 177694469437) := by
    rw [show ((177694469437 / 100000000000) : ℝ) = ((100000000000 / 177694469437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (409427099 / 1000000000) ≤ -Real.log (500000000000 / 752977387517) ∧
    -Real.log (500000000000 / 752977387517) ≤ (4094271 / 10000000) := by
  have h := checkLog_sound (w := (252977387517 / 1252977387517)) (n := 12)
    (lo := (409427099 / 1000000000)) (hi := (4094271 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752977387517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752977387517 / 500000000000) = 1/(500000000000 / 752977387517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (409427099 / 1000000000) (4094271 / 10000000) (Real.log (752977387517 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (752977387517 / 500000000000) = -Real.log (500000000000 / 752977387517) := by
    rw [show ((752977387517 / 500000000000) : ℝ) = ((500000000000 / 752977387517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (410094341 / 1000000000) ≤ -Real.log (250000000000 / 376739986889) ∧
    -Real.log (250000000000 / 376739986889) ≤ (205047171 / 500000000) := by
  have h := checkLog_sound (w := (126739986889 / 626739986889)) (n := 12)
    (lo := (410094341 / 1000000000)) (hi := (205047171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376739986889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376739986889 / 250000000000) = 1/(250000000000 / 376739986889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (410094341 / 1000000000) (205047171 / 500000000) (Real.log (376739986889 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (376739986889 / 250000000000) = -Real.log (250000000000 / 376739986889) := by
    rw [show ((376739986889 / 250000000000) : ℝ) = ((250000000000 / 376739986889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20876491 / 500000000) ≤ -Real.log (959106667159 / 1000000000000) ∧
    -Real.log (959106667159 / 1000000000000) ≤ (41752983 / 1000000000) := by
  have h := checkLog_sound (w := (40893332841 / 1959106667159)) (n := 12)
    (lo := (20876491 / 500000000)) (hi := (41752983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959106667159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959106667159) = 1/(959106667159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41752983 / 1000000000) (-20876491 / 500000000) (Real.log (959106667159 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (41618159 / 1000000000) ≤ -Real.log (959235986199 / 1000000000000) ∧
    -Real.log (959235986199 / 1000000000000) ≤ (520227 / 12500000) := by
  have h := checkLog_sound (w := (40764013801 / 1959235986199)) (n := 12)
    (lo := (41618159 / 1000000000)) (hi := (520227 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959235986199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959235986199) = 1/(959235986199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-520227 / 12500000) (-41618159 / 1000000000) (Real.log (959235986199 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell243

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell244Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell244
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

theorem reflection_log_1_neg : (331857811 / 1000000000) ≤ -Real.log (1024 / 1427) ∧
    -Real.log (1024 / 1427) ≤ (82964453 / 250000000) := by
  have h := checkLog_sound (w := (403 / 2451)) (n := 12)
    (lo := (331857811 / 1000000000)) (hi := (82964453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427 / 1024) = 1/(1024 / 1427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331857811 / 1000000000) (82964453 / 250000000) (Real.log (1427 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1427 / 1024) = -Real.log (1024 / 1427) := by
    rw [show ((1427 / 1024) : ℝ) = ((1024 / 1427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (500140723 / 1000000000) ≤ -Real.log (621 / 1024) ∧
    -Real.log (621 / 1024) ≤ (125035181 / 250000000) := by
  have h := checkLog_sound (w := (403 / 1645)) (n := 12)
    (lo := (500140723 / 1000000000)) (hi := (125035181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 621) = 1/(621 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-125035181 / 250000000) (-500140723 / 1000000000) (Real.log (621 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16571863 / 50000000) ≤ -Real.log (1280 / 1783) ∧
    -Real.log (1280 / 1783) ≤ (331437261 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 3063)) (n := 12)
    (lo := (16571863 / 50000000)) (hi := (331437261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1783 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1783 / 1280) = 1/(1280 / 1783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16571863 / 50000000) (331437261 / 1000000000) (Real.log (1783 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1783 / 1280) = -Real.log (1280 / 1783) := by
    rw [show ((1783 / 1280) : ℝ) = ((1280 / 1783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249587503 / 500000000) ≤ -Real.log (777 / 1280) ∧
    -Real.log (777 / 1280) ≤ (499175007 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2057)) (n := 12)
    (lo := (249587503 / 500000000)) (hi := (499175007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 777) = 1/(777 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-499175007 / 1000000000) (-249587503 / 500000000) (Real.log (777 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (61672633 / 250000000) ≤ -Real.log (1000000 / 1279783) ∧
    -Real.log (1000000 / 1279783) ≤ (246690533 / 1000000000) := by
  have h := checkLog_sound (w := (279783 / 2279783)) (n := 12)
    (lo := (61672633 / 250000000)) (hi := (246690533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279783 / 1000000) = 1/(1000000 / 1279783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (61672633 / 250000000) (246690533 / 1000000000) (Real.log (1279783 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1279783 / 1000000) = -Real.log (1000000 / 1279783) := by
    rw [show ((1279783 / 1000000) : ℝ) = ((1000000 / 1279783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (328202723 / 1000000000) ≤ -Real.log (720217 / 1000000) ∧
    -Real.log (720217 / 1000000) ≤ (82050681 / 250000000) := by
  have h := checkLog_sound (w := (279783 / 1720217)) (n := 12)
    (lo := (328202723 / 1000000000)) (hi := (82050681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720217) = 1/(720217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82050681 / 250000000) (-328202723 / 1000000000) (Real.log (720217 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (247021783 / 1000000000) ≤ -Real.log (1000000 / 1280207) ∧
    -Real.log (1000000 / 1280207) ≤ (30877723 / 125000000) := by
  have h := checkLog_sound (w := (280207 / 2280207)) (n := 12)
    (lo := (247021783 / 1000000000)) (hi := (30877723 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280207 / 1000000) = 1/(1000000 / 1280207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (247021783 / 1000000000) (30877723 / 125000000) (Real.log (1280207 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1280207 / 1000000) = -Real.log (1000000 / 1280207) := by
    rw [show ((1280207 / 1000000) : ℝ) = ((1000000 / 1280207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (41098951 / 125000000) ≤ -Real.log (719793 / 1000000) ∧
    -Real.log (719793 / 1000000) ≤ (328791609 / 1000000000) := by
  have h := checkLog_sound (w := (280207 / 1719793)) (n := 12)
    (lo := (41098951 / 125000000)) (hi := (328791609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 719793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 719793) = 1/(719793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-328791609 / 1000000000) (-41098951 / 125000000) (Real.log (719793 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (184169847 / 1000000000) ≤ -Real.log (50000 / 60111) ∧
    -Real.log (50000 / 60111) ≤ (23021231 / 125000000) := by
  have h := checkLog_sound (w := (10111 / 110111)) (n := 12)
    (lo := (184169847 / 1000000000)) (hi := (23021231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60111 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60111 / 50000) = 1/(50000 / 60111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (184169847 / 1000000000) (23021231 / 125000000) (Real.log (60111 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (60111 / 50000) = -Real.log (50000 / 60111) := by
    rw [show ((60111 / 50000) : ℝ) = ((50000 / 60111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (28240301 / 125000000) ≤ -Real.log (39889 / 50000) ∧
    -Real.log (39889 / 50000) ≤ (225922409 / 1000000000) := by
  have h := checkLog_sound (w := (10111 / 89889)) (n := 12)
    (lo := (28240301 / 125000000)) (hi := (225922409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39889) = 1/(39889 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225922409 / 1000000000) (-28240301 / 125000000) (Real.log (39889 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92218409 / 500000000) ≤ -Real.log (1000000 / 1202541) ∧
    -Real.log (1000000 / 1202541) ≤ (184436819 / 1000000000) := by
  have h := checkLog_sound (w := (202541 / 2202541)) (n := 12)
    (lo := (92218409 / 500000000)) (hi := (184436819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202541 / 1000000) = 1/(1000000 / 1202541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92218409 / 500000000) (184436819 / 1000000000) (Real.log (1202541 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1202541 / 1000000) = -Real.log (1000000 / 1202541) := by
    rw [show ((1202541 / 1000000) : ℝ) = ((1000000 / 1202541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28290607 / 125000000) ≤ -Real.log (797459 / 1000000) ∧
    -Real.log (797459 / 1000000) ≤ (226324857 / 1000000000) := by
  have h := checkLog_sound (w := (202541 / 1797459)) (n := 12)
    (lo := (28290607 / 125000000)) (hi := (226324857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797459) = 1/(797459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-226324857 / 1000000000) (-28290607 / 125000000) (Real.log (797459 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (415306133 / 500000000) ≤ -Real.log (500000000000 / 1147361647361) ∧
    -Real.log (500000000000 / 1147361647361) ≤ (207653067 / 250000000) := by
  have h := checkLog_sound (w := (147361647361 / 2147361647361)) (n := 12)
    (lo := (68732543 / 500000000)) (hi := (137465087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147361647361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1147361647361 / 1000000000000) = 1/(500000000000 / 1147361647361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (415306133 / 500000000) (207653067 / 250000000) (Real.log (1147361647361 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1147361647361 / 500000000000) = -Real.log (500000000000 / 1147361647361) := by
    rw [show ((1147361647361 / 500000000000) : ℝ) = ((500000000000 / 1147361647361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (415999267 / 500000000) ≤ -Real.log (62500000000 / 143619162641) ∧
    -Real.log (62500000000 / 143619162641) ≤ (103999817 / 125000000) := by
  have h := checkLog_sound (w := (18619162641 / 268619162641)) (n := 12)
    (lo := (69425677 / 500000000)) (hi := (27770271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143619162641 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(143619162641 / 125000000000) = 1/(62500000000 / 143619162641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (415999267 / 500000000) (103999817 / 125000000) (Real.log (143619162641 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (143619162641 / 62500000000) = -Real.log (62500000000 / 143619162641) := by
    rw [show ((143619162641 / 62500000000) : ℝ) = ((62500000000 / 143619162641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (114978651 / 200000000) ≤ -Real.log (500000000000 / 888470419331) ∧
    -Real.log (500000000000 / 888470419331) ≤ (71861657 / 125000000) := by
  have h := checkLog_sound (w := (388470419331 / 1388470419331)) (n := 12)
    (lo := (114978651 / 200000000)) (hi := (71861657 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((888470419331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(888470419331 / 500000000000) = 1/(500000000000 / 888470419331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114978651 / 200000000) (71861657 / 125000000) (Real.log (888470419331 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (888470419331 / 500000000000) = -Real.log (500000000000 / 888470419331) := by
    rw [show ((888470419331 / 500000000000) : ℝ) = ((500000000000 / 888470419331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (575813391 / 1000000000) ≤ -Real.log (250000000000 / 444644154639) ∧
    -Real.log (250000000000 / 444644154639) ≤ (35988337 / 62500000) := by
  have h := checkLog_sound (w := (194644154639 / 694644154639)) (n := 12)
    (lo := (575813391 / 1000000000)) (hi := (35988337 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444644154639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444644154639 / 250000000000) = 1/(250000000000 / 444644154639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (575813391 / 1000000000) (35988337 / 62500000) (Real.log (444644154639 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (444644154639 / 250000000000) = -Real.log (250000000000 / 444644154639) := by
    rw [show ((444644154639 / 250000000000) : ℝ) = ((250000000000 / 444644154639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (12815383 / 31250000) ≤ -Real.log (500000000000 / 753478402567) ∧
    -Real.log (500000000000 / 753478402567) ≤ (410092257 / 1000000000) := by
  have h := checkLog_sound (w := (253478402567 / 1253478402567)) (n := 12)
    (lo := (12815383 / 31250000)) (hi := (410092257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753478402567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753478402567 / 500000000000) = 1/(500000000000 / 753478402567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (12815383 / 31250000) (410092257 / 1000000000) (Real.log (753478402567 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (753478402567 / 500000000000) = -Real.log (500000000000 / 753478402567) := by
    rw [show ((753478402567 / 500000000000) : ℝ) = ((500000000000 / 753478402567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (205380837 / 500000000) ≤ -Real.log (125000000000 / 188495740847) ∧
    -Real.log (125000000000 / 188495740847) ≤ (16430467 / 40000000) := by
  have h := checkLog_sound (w := (63495740847 / 313495740847)) (n := 12)
    (lo := (205380837 / 500000000)) (hi := (16430467 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188495740847 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188495740847 / 125000000000) = 1/(125000000000 / 188495740847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (205380837 / 500000000) (16430467 / 40000000) (Real.log (188495740847 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (188495740847 / 125000000000) = -Real.log (125000000000 / 188495740847) := by
    rw [show ((188495740847 / 125000000000) : ℝ) = ((125000000000 / 188495740847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20944019 / 500000000) ≤ -Real.log (958977143319 / 1000000000000) ∧
    -Real.log (958977143319 / 1000000000000) ≤ (41888039 / 1000000000) := by
  have h := checkLog_sound (w := (41022856681 / 1958977143319)) (n := 12)
    (lo := (20944019 / 500000000)) (hi := (41888039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958977143319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958977143319) = 1/(958977143319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41888039 / 1000000000) (-20944019 / 500000000) (Real.log (958977143319 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (41752561 / 1000000000) ≤ -Real.log (2397767679 / 2500000000) ∧
    -Real.log (2397767679 / 2500000000) ≤ (20876281 / 500000000) := by
  have h := checkLog_sound (w := (102232321 / 4897767679)) (n := 12)
    (lo := (41752561 / 1000000000)) (hi := (20876281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2397767679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2397767679) = 1/(2397767679 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20876281 / 500000000) (-41752561 / 1000000000) (Real.log (2397767679 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell244

end


