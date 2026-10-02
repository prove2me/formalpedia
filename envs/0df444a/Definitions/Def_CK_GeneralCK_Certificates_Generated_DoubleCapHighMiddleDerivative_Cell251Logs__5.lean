-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell251Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell251Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:11:11.847283+00:00
-- url     : https://prove2.me/theorems/1dcc679c-ea0b-44e3-a9ab-b0234216f186
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell251Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell252…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell251Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell252Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell253Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell254Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell255Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell251Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell252Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell253Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell254Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell255Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell251Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell252Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell253Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell254Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell255Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell251Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell252Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell253Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell254Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell255Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell251Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell251
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

theorem reflection_log_1_neg : (167398363 / 500000000) ≤ -Real.log (1280 / 1789) ∧
    -Real.log (1280 / 1789) ≤ (334796727 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 3069)) (n := 12)
    (lo := (167398363 / 500000000)) (hi := (334796727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1789 / 1280) = 1/(1280 / 1789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (167398363 / 500000000) (334796727 / 1000000000) (Real.log (1789 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1789 / 1280) = -Real.log (1280 / 1789) := by
    rw [show ((1789 / 1280) : ℝ) = ((1280 / 1789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (506926983 / 1000000000) ≤ -Real.log (771 / 1280) ∧
    -Real.log (771 / 1280) ≤ (63365873 / 125000000) := by
  have h := checkLog_sound (w := (509 / 2051)) (n := 12)
    (lo := (506926983 / 1000000000)) (hi := (63365873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 771) = 1/(771 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63365873 / 125000000) (-506926983 / 1000000000) (Real.log (771 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33437741 / 100000000) ≤ -Real.log (5120 / 7153) ∧
    -Real.log (5120 / 7153) ≤ (334377411 / 1000000000) := by
  have h := checkLog_sound (w := (2033 / 12273)) (n := 12)
    (lo := (33437741 / 100000000)) (hi := (334377411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7153 / 5120) = 1/(5120 / 7153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33437741 / 100000000) (334377411 / 1000000000) (Real.log (7153 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7153 / 5120) = -Real.log (5120 / 7153) := by
    rw [show ((7153 / 5120) : ℝ) = ((5120 / 7153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (505954693 / 1000000000) ≤ -Real.log (3087 / 5120) ∧
    -Real.log (3087 / 5120) ≤ (252977347 / 500000000) := by
  have h := checkLog_sound (w := (2033 / 8207)) (n := 12)
    (lo := (505954693 / 1000000000)) (hi := (252977347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3087) = 1/(3087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-252977347 / 500000000) (-505954693 / 1000000000) (Real.log (3087 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7781371 / 31250000) ≤ -Real.log (1000000 / 1282747) ∧
    -Real.log (1000000 / 1282747) ≤ (249003873 / 1000000000) := by
  have h := checkLog_sound (w := (282747 / 2282747)) (n := 12)
    (lo := (7781371 / 31250000)) (hi := (249003873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282747 / 1000000) = 1/(1000000 / 1282747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7781371 / 31250000) (249003873 / 1000000000) (Real.log (1282747 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1282747 / 1000000) = -Real.log (1000000 / 1282747) := by
    rw [show ((1282747 / 1000000) : ℝ) = ((1000000 / 1282747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (332326641 / 1000000000) ≤ -Real.log (717253 / 1000000) ∧
    -Real.log (717253 / 1000000) ≤ (166163321 / 500000000) := by
  have h := checkLog_sound (w := (282747 / 1717253)) (n := 12)
    (lo := (332326641 / 1000000000)) (hi := (166163321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717253) = 1/(717253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166163321 / 500000000) (-332326641 / 1000000000) (Real.log (717253 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124667179 / 500000000) ≤ -Real.log (1000000 / 1283171) ∧
    -Real.log (1000000 / 1283171) ≤ (249334359 / 1000000000) := by
  have h := checkLog_sound (w := (283171 / 2283171)) (n := 12)
    (lo := (124667179 / 500000000)) (hi := (249334359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283171 / 1000000) = 1/(1000000 / 1283171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124667179 / 500000000) (249334359 / 1000000000) (Real.log (1283171 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1283171 / 1000000) = -Real.log (1000000 / 1283171) := by
    rw [show ((1283171 / 1000000) : ℝ) = ((1000000 / 1283171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8322949 / 25000000) ≤ -Real.log (716829 / 1000000) ∧
    -Real.log (716829 / 1000000) ≤ (332917961 / 1000000000) := by
  have h := checkLog_sound (w := (283171 / 1716829)) (n := 12)
    (lo := (8322949 / 25000000)) (hi := (332917961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 716829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 716829) = 1/(716829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-332917961 / 1000000000) (-8322949 / 25000000) (Real.log (716829 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (186030503 / 1000000000) ≤ -Real.log (1000000 / 1204459) ∧
    -Real.log (1000000 / 1204459) ≤ (23253813 / 125000000) := by
  have h := checkLog_sound (w := (204459 / 2204459)) (n := 12)
    (lo := (186030503 / 1000000000)) (hi := (23253813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204459 / 1000000) = 1/(1000000 / 1204459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (186030503 / 1000000000) (23253813 / 125000000) (Real.log (1204459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1204459 / 1000000) = -Real.log (1000000 / 1204459) := by
    rw [show ((1204459 / 1000000) : ℝ) = ((1000000 / 1204459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57183223 / 250000000) ≤ -Real.log (795541 / 1000000) ∧
    -Real.log (795541 / 1000000) ≤ (228732893 / 1000000000) := by
  have h := checkLog_sound (w := (204459 / 1795541)) (n := 12)
    (lo := (57183223 / 250000000)) (hi := (228732893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795541) = 1/(795541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-228732893 / 1000000000) (-57183223 / 250000000) (Real.log (795541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186296977 / 1000000000) ≤ -Real.log (50000 / 60239) ∧
    -Real.log (50000 / 60239) ≤ (93148489 / 500000000) := by
  have h := checkLog_sound (w := (10239 / 110239)) (n := 12)
    (lo := (186296977 / 1000000000)) (hi := (93148489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60239 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60239 / 50000) = 1/(50000 / 60239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186296977 / 1000000000) (93148489 / 500000000) (Real.log (60239 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60239 / 50000) = -Real.log (50000 / 60239) := by
    rw [show ((60239 / 50000) : ℝ) = ((50000 / 60239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (229136473 / 1000000000) ≤ -Real.log (39761 / 50000) ∧
    -Real.log (39761 / 50000) ≤ (114568237 / 500000000) := by
  have h := checkLog_sound (w := (10239 / 89761)) (n := 12)
    (lo := (229136473 / 1000000000)) (hi := (114568237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39761) = 1/(39761 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-114568237 / 500000000) (-229136473 / 1000000000) (Real.log (39761 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (840332103 / 1000000000) ≤ -Real.log (25000000000 / 57928409459) ∧
    -Real.log (25000000000 / 57928409459) ≤ (168066421 / 200000000) := by
  have h := checkLog_sound (w := (7928409459 / 107928409459)) (n := 12)
    (lo := (147184923 / 1000000000)) (hi := (36796231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57928409459 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(57928409459 / 50000000000) = 1/(25000000000 / 57928409459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (840332103 / 1000000000) (168066421 / 200000000) (Real.log (57928409459 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (57928409459 / 25000000000) = -Real.log (25000000000 / 57928409459) := by
    rw [show ((57928409459 / 25000000000) : ℝ) = ((25000000000 / 57928409459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (841723709 / 1000000000) ≤ -Real.log (500000000000 / 1160181582361) ∧
    -Real.log (500000000000 / 1160181582361) ≤ (841723711 / 1000000000) := by
  have h := checkLog_sound (w := (160181582361 / 2160181582361)) (n := 12)
    (lo := (148576529 / 1000000000)) (hi := (14857653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160181582361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1160181582361 / 1000000000000) = 1/(500000000000 / 1160181582361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (841723709 / 1000000000) (841723711 / 1000000000) (Real.log (1160181582361 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1160181582361 / 500000000000) = -Real.log (500000000000 / 1160181582361) := by
    rw [show ((1160181582361 / 500000000000) : ℝ) = ((500000000000 / 1160181582361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (581330513 / 1000000000) ≤ -Real.log (500000000000 / 894208180377) ∧
    -Real.log (500000000000 / 894208180377) ≤ (290665257 / 500000000) := by
  have h := checkLog_sound (w := (394208180377 / 1394208180377)) (n := 12)
    (lo := (581330513 / 1000000000)) (hi := (290665257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894208180377 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894208180377 / 500000000000) = 1/(500000000000 / 894208180377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (581330513 / 1000000000) (290665257 / 500000000) (Real.log (894208180377 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (894208180377 / 500000000000) = -Real.log (500000000000 / 894208180377) := by
    rw [show ((894208180377 / 500000000000) : ℝ) = ((500000000000 / 894208180377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (291126159 / 500000000) ≤ -Real.log (500000000000 / 895032846049) ∧
    -Real.log (500000000000 / 895032846049) ≤ (582252319 / 1000000000) := by
  have h := checkLog_sound (w := (395032846049 / 1395032846049)) (n := 12)
    (lo := (291126159 / 500000000)) (hi := (582252319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((895032846049 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(895032846049 / 500000000000) = 1/(500000000000 / 895032846049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (291126159 / 500000000) (582252319 / 1000000000) (Real.log (895032846049 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (895032846049 / 500000000000) = -Real.log (500000000000 / 895032846049) := by
    rw [show ((895032846049 / 500000000000) : ℝ) = ((500000000000 / 895032846049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (103690849 / 250000000) ≤ -Real.log (500000000000 / 757006238521) ∧
    -Real.log (500000000000 / 757006238521) ≤ (414763397 / 1000000000) := by
  have h := checkLog_sound (w := (257006238521 / 1257006238521)) (n := 12)
    (lo := (103690849 / 250000000)) (hi := (414763397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757006238521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757006238521 / 500000000000) = 1/(500000000000 / 757006238521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (103690849 / 250000000) (414763397 / 1000000000) (Real.log (757006238521 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (757006238521 / 500000000000) = -Real.log (500000000000 / 757006238521) := by
    rw [show ((757006238521 / 500000000000) : ℝ) = ((500000000000 / 757006238521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (8308669 / 20000000) ≤ -Real.log (62500000000 / 94689205503) ∧
    -Real.log (62500000000 / 94689205503) ≤ (415433451 / 1000000000) := by
  have h := checkLog_sound (w := (32189205503 / 157189205503)) (n := 12)
    (lo := (8308669 / 20000000)) (hi := (415433451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94689205503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94689205503 / 62500000000) = 1/(62500000000 / 94689205503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (8308669 / 20000000) (415433451 / 1000000000) (Real.log (94689205503 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (94689205503 / 62500000000) = -Real.log (62500000000 / 94689205503) := by
    rw [show ((94689205503 / 62500000000) : ℝ) = ((62500000000 / 94689205503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8567899 / 200000000) ≤ -Real.log (2395162879 / 2500000000) ∧
    -Real.log (2395162879 / 2500000000) ≤ (5354937 / 125000000) := by
  have h := checkLog_sound (w := (104837121 / 4895162879)) (n := 12)
    (lo := (8567899 / 200000000)) (hi := (5354937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2395162879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2395162879) = 1/(2395162879 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5354937 / 125000000) (-8567899 / 200000000) (Real.log (2395162879 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42702389 / 1000000000) ≤ -Real.log (958196517319 / 1000000000000) ∧
    -Real.log (958196517319 / 1000000000000) ≤ (4270239 / 100000000) := by
  have h := checkLog_sound (w := (41803482681 / 1958196517319)) (n := 12)
    (lo := (42702389 / 1000000000)) (hi := (4270239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958196517319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958196517319) = 1/(958196517319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4270239 / 100000000) (-42702389 / 1000000000) (Real.log (958196517319 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell251

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell252Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell252
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

theorem reflection_log_1_neg : (335215867 / 1000000000) ≤ -Real.log (5120 / 7159) ∧
    -Real.log (5120 / 7159) ≤ (83803967 / 250000000) := by
  have h := checkLog_sound (w := (2039 / 12279)) (n := 12)
    (lo := (335215867 / 1000000000)) (hi := (83803967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7159 / 5120) = 1/(5120 / 7159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335215867 / 1000000000) (83803967 / 250000000) (Real.log (7159 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7159 / 5120) = -Real.log (5120 / 7159) := by
    rw [show ((7159 / 5120) : ℝ) = ((5120 / 7159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (507900219 / 1000000000) ≤ -Real.log (3081 / 5120) ∧
    -Real.log (3081 / 5120) ≤ (25395011 / 50000000) := by
  have h := checkLog_sound (w := (2039 / 8201)) (n := 12)
    (lo := (507900219 / 1000000000)) (hi := (25395011 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3081) = 1/(3081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-25395011 / 50000000) (-507900219 / 1000000000) (Real.log (3081 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (167398363 / 500000000) ≤ -Real.log (1280 / 1789) ∧
    -Real.log (1280 / 1789) ≤ (334796727 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 3069)) (n := 12)
    (lo := (167398363 / 500000000)) (hi := (334796727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1789 / 1280) = 1/(1280 / 1789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (167398363 / 500000000) (334796727 / 1000000000) (Real.log (1789 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1789 / 1280) = -Real.log (1280 / 1789) := by
    rw [show ((1789 / 1280) : ℝ) = ((1280 / 1789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (506926983 / 1000000000) ≤ -Real.log (771 / 1280) ∧
    -Real.log (771 / 1280) ≤ (63365873 / 125000000) := by
  have h := checkLog_sound (w := (509 / 2051)) (n := 12)
    (lo := (506926983 / 1000000000)) (hi := (63365873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 771) = 1/(771 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63365873 / 125000000) (-506926983 / 1000000000) (Real.log (771 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124666789 / 500000000) ≤ -Real.log (100000 / 128317) ∧
    -Real.log (100000 / 128317) ≤ (249333579 / 1000000000) := by
  have h := checkLog_sound (w := (28317 / 228317)) (n := 12)
    (lo := (124666789 / 500000000)) (hi := (249333579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128317 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128317 / 100000) = 1/(100000 / 128317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124666789 / 500000000) (249333579 / 1000000000) (Real.log (128317 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (128317 / 100000) = -Real.log (100000 / 128317) := by
    rw [show ((128317 / 100000) : ℝ) = ((100000 / 128317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (66583313 / 200000000) ≤ -Real.log (71683 / 100000) ∧
    -Real.log (71683 / 100000) ≤ (166458283 / 500000000) := by
  have h := checkLog_sound (w := (28317 / 171683)) (n := 12)
    (lo := (66583313 / 200000000)) (hi := (166458283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 71683) = 1/(71683 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166458283 / 500000000) (-66583313 / 200000000) (Real.log (71683 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124832367 / 500000000) ≤ -Real.log (200000 / 256719) ∧
    -Real.log (200000 / 256719) ≤ (49932947 / 200000000) := by
  have h := checkLog_sound (w := (56719 / 456719)) (n := 12)
    (lo := (124832367 / 500000000)) (hi := (49932947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256719 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256719 / 200000) = 1/(200000 / 256719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124832367 / 500000000) (49932947 / 200000000) (Real.log (256719 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (256719 / 200000) = -Real.log (200000 / 256719) := by
    rw [show ((256719 / 200000) : ℝ) = ((200000 / 256719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (333509629 / 1000000000) ≤ -Real.log (143281 / 200000) ∧
    -Real.log (143281 / 200000) ≤ (33350963 / 100000000) := by
  have h := checkLog_sound (w := (56719 / 343281)) (n := 12)
    (lo := (333509629 / 1000000000)) (hi := (33350963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 143281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 143281) = 1/(143281 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-33350963 / 100000000) (-333509629 / 1000000000) (Real.log (143281 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (186296147 / 1000000000) ≤ -Real.log (1000000 / 1204779) ∧
    -Real.log (1000000 / 1204779) ≤ (46574037 / 250000000) := by
  have h := checkLog_sound (w := (204779 / 2204779)) (n := 12)
    (lo := (186296147 / 1000000000)) (hi := (46574037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204779 / 1000000) = 1/(1000000 / 1204779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (186296147 / 1000000000) (46574037 / 250000000) (Real.log (1204779 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1204779 / 1000000) = -Real.log (1000000 / 1204779) := by
    rw [show ((1204779 / 1000000) : ℝ) = ((1000000 / 1204779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (45827043 / 200000000) ≤ -Real.log (795221 / 1000000) ∧
    -Real.log (795221 / 1000000) ≤ (14320951 / 62500000) := by
  have h := checkLog_sound (w := (204779 / 1795221)) (n := 12)
    (lo := (45827043 / 200000000)) (hi := (14320951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795221) = 1/(795221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14320951 / 62500000) (-45827043 / 200000000) (Real.log (795221 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186562551 / 1000000000) ≤ -Real.log (10000 / 12051) ∧
    -Real.log (10000 / 12051) ≤ (23320319 / 125000000) := by
  have h := checkLog_sound (w := (2051 / 22051)) (n := 12)
    (lo := (186562551 / 1000000000)) (hi := (23320319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12051 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12051 / 10000) = 1/(10000 / 12051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186562551 / 1000000000) (23320319 / 125000000) (Real.log (12051 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (12051 / 10000) = -Real.log (10000 / 12051) := by
    rw [show ((12051 / 10000) : ℝ) = ((10000 / 12051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (114769479 / 500000000) ≤ -Real.log (7949 / 10000) ∧
    -Real.log (7949 / 10000) ≤ (229538959 / 1000000000) := by
  have h := checkLog_sound (w := (2051 / 17949)) (n := 12)
    (lo := (114769479 / 500000000)) (hi := (229538959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7949) = 1/(7949 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-229538959 / 1000000000) (-114769479 / 500000000) (Real.log (7949 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (841723709 / 1000000000) ≤ -Real.log (12500000000 / 29004539559) ∧
    -Real.log (12500000000 / 29004539559) ≤ (841723711 / 1000000000) := by
  have h := checkLog_sound (w := (4004539559 / 54004539559)) (n := 12)
    (lo := (148576529 / 1000000000)) (hi := (14857653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29004539559 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(29004539559 / 25000000000) = 1/(12500000000 / 29004539559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (841723709 / 1000000000) (841723711 / 1000000000) (Real.log (29004539559 / 12500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (29004539559 / 12500000000) = -Real.log (12500000000 / 29004539559) := by
    rw [show ((29004539559 / 12500000000) : ℝ) = ((12500000000 / 29004539559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (421558043 / 500000000) ≤ -Real.log (100000000000 / 232359623499) ∧
    -Real.log (100000000000 / 232359623499) ≤ (105389511 / 125000000) := by
  have h := checkLog_sound (w := (32359623499 / 432359623499)) (n := 12)
    (lo := (74984453 / 500000000)) (hi := (149968907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232359623499 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(232359623499 / 200000000000) = 1/(100000000000 / 232359623499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (421558043 / 500000000) (105389511 / 125000000) (Real.log (232359623499 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (232359623499 / 100000000000) = -Real.log (100000000000 / 232359623499) := by
    rw [show ((232359623499 / 100000000000) : ℝ) = ((100000000000 / 232359623499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (18195317 / 31250000) ≤ -Real.log (250000000000 / 447515449967) ∧
    -Real.log (250000000000 / 447515449967) ≤ (116450029 / 200000000) := by
  have h := checkLog_sound (w := (197515449967 / 697515449967)) (n := 12)
    (lo := (18195317 / 31250000)) (hi := (116450029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447515449967 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447515449967 / 250000000000) = 1/(250000000000 / 447515449967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18195317 / 31250000) (116450029 / 200000000) (Real.log (447515449967 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (447515449967 / 250000000000) = -Real.log (250000000000 / 447515449967) := by
    rw [show ((447515449967 / 250000000000) : ℝ) = ((250000000000 / 447515449967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (145793591 / 250000000) ≤ -Real.log (500000000000 / 895858487867) ∧
    -Real.log (500000000000 / 895858487867) ≤ (116634873 / 200000000) := by
  have h := checkLog_sound (w := (395858487867 / 1395858487867)) (n := 12)
    (lo := (145793591 / 250000000)) (hi := (116634873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((895858487867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(895858487867 / 500000000000) = 1/(500000000000 / 895858487867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (145793591 / 250000000) (116634873 / 200000000) (Real.log (895858487867 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (895858487867 / 500000000000) = -Real.log (500000000000 / 895858487867) := by
    rw [show ((895858487867 / 500000000000) : ℝ) = ((500000000000 / 895858487867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (415431363 / 1000000000) ≤ -Real.log (125000000000 / 189378015671) ∧
    -Real.log (125000000000 / 189378015671) ≤ (103857841 / 250000000) := by
  have h := checkLog_sound (w := (64378015671 / 314378015671)) (n := 12)
    (lo := (415431363 / 1000000000)) (hi := (103857841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189378015671 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189378015671 / 125000000000) = 1/(125000000000 / 189378015671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (415431363 / 1000000000) (103857841 / 250000000) (Real.log (189378015671 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (189378015671 / 125000000000) = -Real.log (125000000000 / 189378015671) := by
    rw [show ((189378015671 / 125000000000) : ℝ) = ((125000000000 / 189378015671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (416101509 / 1000000000) ≤ -Real.log (100000000000 / 151603975343) ∧
    -Real.log (100000000000 / 151603975343) ≤ (41610151 / 100000000) := by
  have h := checkLog_sound (w := (51603975343 / 251603975343)) (n := 12)
    (lo := (416101509 / 1000000000)) (hi := (41610151 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151603975343 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151603975343 / 100000000000) = 1/(100000000000 / 151603975343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (416101509 / 1000000000) (41610151 / 100000000) (Real.log (151603975343 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (151603975343 / 100000000000) = -Real.log (100000000000 / 151603975343) := by
    rw [show ((151603975343 / 100000000000) : ℝ) = ((100000000000 / 151603975343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42976407 / 1000000000) ≤ -Real.log (95793399 / 100000000) ∧
    -Real.log (95793399 / 100000000) ≤ (5372051 / 125000000) := by
  have h := checkLog_sound (w := (4206601 / 195793399)) (n := 12)
    (lo := (42976407 / 1000000000)) (hi := (5372051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 95793399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 95793399) = 1/(95793399 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5372051 / 125000000) (-42976407 / 1000000000) (Real.log (95793399 / 100000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42839067 / 1000000000) ≤ -Real.log (958065561159 / 1000000000000) ∧
    -Real.log (958065561159 / 1000000000000) ≤ (10709767 / 250000000) := by
  have h := checkLog_sound (w := (41934438841 / 1958065561159)) (n := 12)
    (lo := (42839067 / 1000000000)) (hi := (10709767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958065561159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958065561159) = 1/(958065561159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10709767 / 250000000) (-42839067 / 1000000000) (Real.log (958065561159 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell252

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell253Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell253
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

theorem reflection_log_1_neg : (20977177 / 62500000) ≤ -Real.log (2560 / 3581) ∧
    -Real.log (2560 / 3581) ≤ (335634833 / 1000000000) := by
  have h := checkLog_sound (w := (1021 / 6141)) (n := 12)
    (lo := (20977177 / 62500000)) (hi := (335634833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3581 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3581 / 2560) = 1/(2560 / 3581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20977177 / 62500000) (335634833 / 1000000000) (Real.log (3581 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3581 / 2560) = -Real.log (2560 / 3581) := by
    rw [show ((3581 / 2560) : ℝ) = ((2560 / 3581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (508874403 / 1000000000) ≤ -Real.log (1539 / 2560) ∧
    -Real.log (1539 / 2560) ≤ (127218601 / 250000000) := by
  have h := checkLog_sound (w := (1021 / 4099)) (n := 12)
    (lo := (508874403 / 1000000000)) (hi := (127218601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1539) = 1/(1539 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127218601 / 250000000) (-508874403 / 1000000000) (Real.log (1539 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335215867 / 1000000000) ≤ -Real.log (5120 / 7159) ∧
    -Real.log (5120 / 7159) ≤ (83803967 / 250000000) := by
  have h := checkLog_sound (w := (2039 / 12279)) (n := 12)
    (lo := (335215867 / 1000000000)) (hi := (83803967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7159 / 5120) = 1/(5120 / 7159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335215867 / 1000000000) (83803967 / 250000000) (Real.log (7159 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7159 / 5120) = -Real.log (5120 / 7159) := by
    rw [show ((7159 / 5120) : ℝ) = ((5120 / 7159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (507900219 / 1000000000) ≤ -Real.log (3081 / 5120) ∧
    -Real.log (3081 / 5120) ≤ (25395011 / 50000000) := by
  have h := checkLog_sound (w := (2039 / 8201)) (n := 12)
    (lo := (507900219 / 1000000000)) (hi := (25395011 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3081) = 1/(3081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-25395011 / 50000000) (-507900219 / 1000000000) (Real.log (3081 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49932791 / 200000000) ≤ -Real.log (500000 / 641797) ∧
    -Real.log (500000 / 641797) ≤ (62415989 / 250000000) := by
  have h := checkLog_sound (w := (141797 / 1141797)) (n := 12)
    (lo := (49932791 / 200000000)) (hi := (62415989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641797 / 500000) = 1/(500000 / 641797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49932791 / 200000000) (62415989 / 250000000) (Real.log (641797 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (641797 / 500000) = -Real.log (500000 / 641797) := by
    rw [show ((641797 / 500000) : ℝ) = ((500000 / 641797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (333508233 / 1000000000) ≤ -Real.log (358203 / 500000) ∧
    -Real.log (358203 / 500000) ≤ (166754117 / 500000000) := by
  have h := checkLog_sound (w := (141797 / 858203)) (n := 12)
    (lo := (333508233 / 1000000000)) (hi := (166754117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 358203) = 1/(358203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166754117 / 500000000) (-333508233 / 1000000000) (Real.log (358203 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (249994223 / 1000000000) ≤ -Real.log (500000 / 642009) ∧
    -Real.log (500000 / 642009) ≤ (15624639 / 62500000) := by
  have h := checkLog_sound (w := (142009 / 1142009)) (n := 12)
    (lo := (249994223 / 1000000000)) (hi := (15624639 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642009 / 500000) = 1/(500000 / 642009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (249994223 / 1000000000) (15624639 / 62500000) (Real.log (642009 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (642009 / 500000) = -Real.log (500000 / 642009) := by
    rw [show ((642009 / 500000) : ℝ) = ((500000 / 642009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (83525063 / 250000000) ≤ -Real.log (357991 / 500000) ∧
    -Real.log (357991 / 500000) ≤ (334100253 / 1000000000) := by
  have h := checkLog_sound (w := (142009 / 857991)) (n := 12)
    (lo := (83525063 / 250000000)) (hi := (334100253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357991) = 1/(357991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-334100253 / 1000000000) (-83525063 / 250000000) (Real.log (357991 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (186561721 / 1000000000) ≤ -Real.log (1000000 / 1205099) ∧
    -Real.log (1000000 / 1205099) ≤ (93280861 / 500000000) := by
  have h := checkLog_sound (w := (205099 / 2205099)) (n := 12)
    (lo := (186561721 / 1000000000)) (hi := (93280861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205099 / 1000000) = 1/(1000000 / 1205099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (186561721 / 1000000000) (93280861 / 500000000) (Real.log (1205099 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1205099 / 1000000) = -Real.log (1000000 / 1205099) := by
    rw [show ((1205099 / 1000000) : ℝ) = ((1000000 / 1205099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2295377 / 10000000) ≤ -Real.log (794901 / 1000000) ∧
    -Real.log (794901 / 1000000) ≤ (229537701 / 1000000000) := by
  have h := checkLog_sound (w := (205099 / 1794901)) (n := 12)
    (lo := (2295377 / 10000000)) (hi := (229537701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794901) = 1/(794901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-229537701 / 1000000000) (-2295377 / 10000000) (Real.log (794901 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186828053 / 1000000000) ≤ -Real.log (50000 / 60271) ∧
    -Real.log (50000 / 60271) ≤ (93414027 / 500000000) := by
  have h := checkLog_sound (w := (10271 / 110271)) (n := 12)
    (lo := (186828053 / 1000000000)) (hi := (93414027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60271 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60271 / 50000) = 1/(50000 / 60271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186828053 / 1000000000) (93414027 / 500000000) (Real.log (60271 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60271 / 50000) = -Real.log (50000 / 60271) := by
    rw [show ((60271 / 50000) : ℝ) = ((50000 / 60271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (45988321 / 200000000) ≤ -Real.log (39729 / 50000) ∧
    -Real.log (39729 / 50000) ≤ (114970803 / 500000000) := by
  have h := checkLog_sound (w := (10271 / 89729)) (n := 12)
    (lo := (45988321 / 200000000)) (hi := (114970803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39729) = 1/(39729 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-114970803 / 500000000) (-45988321 / 200000000) (Real.log (39729 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (421558043 / 500000000) ≤ -Real.log (250000000000 / 580899058747) ∧
    -Real.log (250000000000 / 580899058747) ≤ (105389511 / 125000000) := by
  have h := checkLog_sound (w := (80899058747 / 1080899058747)) (n := 12)
    (lo := (74984453 / 500000000)) (hi := (149968907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580899058747 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(580899058747 / 500000000000) = 1/(250000000000 / 580899058747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (421558043 / 500000000) (105389511 / 125000000) (Real.log (580899058747 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (580899058747 / 250000000000) = -Real.log (250000000000 / 580899058747) := by
    rw [show ((580899058747 / 250000000000) : ℝ) = ((250000000000 / 580899058747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (168901847 / 200000000) ≤ -Real.log (500000000000 / 1163417803769) ∧
    -Real.log (500000000000 / 1163417803769) ≤ (844509237 / 1000000000) := by
  have h := checkLog_sound (w := (163417803769 / 2163417803769)) (n := 12)
    (lo := (30272411 / 200000000)) (hi := (18920257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163417803769 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1163417803769 / 1000000000000) = 1/(500000000000 / 1163417803769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (168901847 / 200000000) (844509237 / 1000000000) (Real.log (1163417803769 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1163417803769 / 500000000000) = -Real.log (500000000000 / 1163417803769) := by
    rw [show ((1163417803769 / 500000000000) : ℝ) = ((500000000000 / 1163417803769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (583172189 / 1000000000) ≤ -Real.log (62500000000 / 111982067431) ∧
    -Real.log (62500000000 / 111982067431) ≤ (58317219 / 100000000) := by
  have h := checkLog_sound (w := (49482067431 / 174482067431)) (n := 12)
    (lo := (583172189 / 1000000000)) (hi := (58317219 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111982067431 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111982067431 / 62500000000) = 1/(62500000000 / 111982067431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (583172189 / 1000000000) (58317219 / 100000000) (Real.log (111982067431 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (111982067431 / 62500000000) = -Real.log (62500000000 / 111982067431) := by
    rw [show ((111982067431 / 62500000000) : ℝ) = ((62500000000 / 111982067431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23363779 / 40000000) ≤ -Real.log (12500000000 / 22417078921) ∧
    -Real.log (12500000000 / 22417078921) ≤ (146023619 / 250000000) := by
  have h := checkLog_sound (w := (9917078921 / 34917078921)) (n := 12)
    (lo := (23363779 / 40000000)) (hi := (146023619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22417078921 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22417078921 / 12500000000) = 1/(12500000000 / 22417078921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (23363779 / 40000000) (146023619 / 250000000) (Real.log (22417078921 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (22417078921 / 12500000000) = -Real.log (12500000000 / 22417078921) := by
    rw [show ((22417078921 / 12500000000) : ℝ) = ((12500000000 / 22417078921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (416099421 / 1000000000) ≤ -Real.log (250000000000 / 379009147051) ∧
    -Real.log (250000000000 / 379009147051) ≤ (208049711 / 500000000) := by
  have h := checkLog_sound (w := (129009147051 / 629009147051)) (n := 12)
    (lo := (416099421 / 1000000000)) (hi := (208049711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379009147051 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379009147051 / 250000000000) = 1/(250000000000 / 379009147051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (416099421 / 1000000000) (208049711 / 500000000) (Real.log (379009147051 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (379009147051 / 250000000000) = -Real.log (250000000000 / 379009147051) := by
    rw [show ((379009147051 / 250000000000) : ℝ) = ((250000000000 / 379009147051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (416769659 / 1000000000) ≤ -Real.log (250000000000 / 379263258577) ∧
    -Real.log (250000000000 / 379263258577) ≤ (20838483 / 50000000) := by
  have h := checkLog_sound (w := (129263258577 / 629263258577)) (n := 12)
    (lo := (416769659 / 1000000000)) (hi := (20838483 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379263258577 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379263258577 / 250000000000) = 1/(250000000000 / 379263258577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (416769659 / 1000000000) (20838483 / 50000000) (Real.log (379263258577 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (379263258577 / 250000000000) = -Real.log (250000000000 / 379263258577) := by
    rw [show ((379263258577 / 250000000000) : ℝ) = ((250000000000 / 379263258577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43113551 / 1000000000) ≤ -Real.log (2394506559 / 2500000000) ∧
    -Real.log (2394506559 / 2500000000) ≤ (2694597 / 62500000) := by
  have h := checkLog_sound (w := (105493441 / 4894506559)) (n := 12)
    (lo := (43113551 / 1000000000)) (hi := (2694597 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2394506559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2394506559) = 1/(2394506559 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2694597 / 62500000) (-43113551 / 1000000000) (Real.log (2394506559 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42975979 / 1000000000) ≤ -Real.log (957934400199 / 1000000000000) ∧
    -Real.log (957934400199 / 1000000000000) ≤ (2148799 / 50000000) := by
  have h := checkLog_sound (w := (42065599801 / 1957934400199)) (n := 12)
    (lo := (42975979 / 1000000000)) (hi := (2148799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957934400199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957934400199) = 1/(957934400199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2148799 / 50000000) (-42975979 / 1000000000) (Real.log (957934400199 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell253

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell254Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell254
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

theorem reflection_log_1_neg : (168026811 / 500000000) ≤ -Real.log (1024 / 1433) ∧
    -Real.log (1024 / 1433) ≤ (336053623 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2457)) (n := 12)
    (lo := (168026811 / 500000000)) (hi := (336053623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433 / 1024) = 1/(1024 / 1433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (168026811 / 500000000) (336053623 / 1000000000) (Real.log (1433 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1433 / 1024) = -Real.log (1024 / 1433) := by
    rw [show ((1433 / 1024) : ℝ) = ((1024 / 1433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (509849537 / 1000000000) ≤ -Real.log (615 / 1024) ∧
    -Real.log (615 / 1024) ≤ (254924769 / 500000000) := by
  have h := checkLog_sound (w := (409 / 1639)) (n := 12)
    (lo := (509849537 / 1000000000)) (hi := (254924769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 615) = 1/(615 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-254924769 / 500000000) (-509849537 / 1000000000) (Real.log (615 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20977177 / 62500000) ≤ -Real.log (2560 / 3581) ∧
    -Real.log (2560 / 3581) ≤ (335634833 / 1000000000) := by
  have h := checkLog_sound (w := (1021 / 6141)) (n := 12)
    (lo := (20977177 / 62500000)) (hi := (335634833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3581 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3581 / 2560) = 1/(2560 / 3581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20977177 / 62500000) (335634833 / 1000000000) (Real.log (3581 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3581 / 2560) = -Real.log (2560 / 3581) := by
    rw [show ((3581 / 2560) : ℝ) = ((2560 / 3581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (508874403 / 1000000000) ≤ -Real.log (1539 / 2560) ∧
    -Real.log (1539 / 2560) ≤ (127218601 / 250000000) := by
  have h := checkLog_sound (w := (1021 / 4099)) (n := 12)
    (lo := (508874403 / 1000000000)) (hi := (127218601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1539) = 1/(1539 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127218601 / 250000000) (-508874403 / 1000000000) (Real.log (1539 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49998689 / 200000000) ≤ -Real.log (1000000 / 1284017) ∧
    -Real.log (1000000 / 1284017) ≤ (124996723 / 500000000) := by
  have h := checkLog_sound (w := (284017 / 2284017)) (n := 12)
    (lo := (49998689 / 200000000)) (hi := (124996723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1284017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1284017 / 1000000) = 1/(1000000 / 1284017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49998689 / 200000000) (124996723 / 500000000) (Real.log (1284017 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1284017 / 1000000) = -Real.log (1000000 / 1284017) := by
    rw [show ((1284017 / 1000000) : ℝ) = ((1000000 / 1284017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (66819771 / 200000000) ≤ -Real.log (715983 / 1000000) ∧
    -Real.log (715983 / 1000000) ≤ (41762357 / 125000000) := by
  have h := checkLog_sound (w := (284017 / 1715983)) (n := 12)
    (lo := (66819771 / 200000000)) (hi := (41762357 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 715983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 715983) = 1/(715983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41762357 / 125000000) (-66819771 / 200000000) (Real.log (715983 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (125162191 / 500000000) ≤ -Real.log (500000 / 642221) ∧
    -Real.log (500000 / 642221) ≤ (250324383 / 1000000000) := by
  have h := checkLog_sound (w := (142221 / 1142221)) (n := 12)
    (lo := (125162191 / 500000000)) (hi := (250324383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642221 / 500000) = 1/(500000 / 642221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (125162191 / 500000000) (250324383 / 1000000000) (Real.log (642221 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (642221 / 500000) = -Real.log (500000 / 642221) := by
    rw [show ((642221 / 500000) : ℝ) = ((500000 / 642221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (334692621 / 1000000000) ≤ -Real.log (357779 / 500000) ∧
    -Real.log (357779 / 500000) ≤ (167346311 / 500000000) := by
  have h := checkLog_sound (w := (142221 / 857779)) (n := 12)
    (lo := (334692621 / 1000000000)) (hi := (167346311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357779) = 1/(357779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-167346311 / 500000000) (-334692621 / 1000000000) (Real.log (357779 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (23353403 / 125000000) ≤ -Real.log (1000000 / 1205419) ∧
    -Real.log (1000000 / 1205419) ≤ (7473089 / 40000000) := by
  have h := checkLog_sound (w := (205419 / 2205419)) (n := 12)
    (lo := (23353403 / 125000000)) (hi := (7473089 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205419 / 1000000) = 1/(1000000 / 1205419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (23353403 / 125000000) (7473089 / 40000000) (Real.log (1205419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1205419 / 1000000) = -Real.log (1000000 / 1205419) := by
    rw [show ((1205419 / 1000000) : ℝ) = ((1000000 / 1205419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (229940347 / 1000000000) ≤ -Real.log (794581 / 1000000) ∧
    -Real.log (794581 / 1000000) ≤ (57485087 / 250000000) := by
  have h := checkLog_sound (w := (205419 / 1794581)) (n := 12)
    (lo := (229940347 / 1000000000)) (hi := (57485087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794581) = 1/(794581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-57485087 / 250000000) (-229940347 / 1000000000) (Real.log (794581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37418863 / 200000000) ≤ -Real.log (1000000 / 1205741) ∧
    -Real.log (1000000 / 1205741) ≤ (46773579 / 250000000) := by
  have h := checkLog_sound (w := (205741 / 2205741)) (n := 12)
    (lo := (37418863 / 200000000)) (hi := (46773579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205741 / 1000000) = 1/(1000000 / 1205741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37418863 / 200000000) (46773579 / 250000000) (Real.log (1205741 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1205741 / 1000000) = -Real.log (1000000 / 1205741) := by
    rw [show ((1205741 / 1000000) : ℝ) = ((1000000 / 1205741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (115172837 / 500000000) ≤ -Real.log (794259 / 1000000) ∧
    -Real.log (794259 / 1000000) ≤ (9213827 / 40000000) := by
  have h := checkLog_sound (w := (205741 / 1794259)) (n := 12)
    (lo := (115172837 / 500000000)) (hi := (9213827 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794259) = 1/(794259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9213827 / 40000000) (-115172837 / 500000000) (Real.log (794259 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (168901847 / 200000000) ≤ -Real.log (62500000000 / 145427225471) ∧
    -Real.log (62500000000 / 145427225471) ≤ (844509237 / 1000000000) := by
  have h := checkLog_sound (w := (20427225471 / 270427225471)) (n := 12)
    (lo := (30272411 / 200000000)) (hi := (18920257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145427225471 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(145427225471 / 125000000000) = 1/(62500000000 / 145427225471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (168901847 / 200000000) (844509237 / 1000000000) (Real.log (145427225471 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (145427225471 / 62500000000) = -Real.log (62500000000 / 145427225471) := by
    rw [show ((145427225471 / 62500000000) : ℝ) = ((62500000000 / 145427225471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (845903159 / 1000000000) ≤ -Real.log (500000000000 / 1165040650407) ∧
    -Real.log (500000000000 / 1165040650407) ≤ (845903161 / 1000000000) := by
  have h := checkLog_sound (w := (165040650407 / 2165040650407)) (n := 12)
    (lo := (152755979 / 1000000000)) (hi := (7637799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165040650407 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1165040650407 / 1000000000000) = 1/(500000000000 / 1165040650407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (845903159 / 1000000000) (845903161 / 1000000000) (Real.log (1165040650407 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1165040650407 / 500000000000) = -Real.log (500000000000 / 1165040650407) := by
    rw [show ((1165040650407 / 500000000000) : ℝ) = ((500000000000 / 1165040650407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (5840923 / 10000000) ≤ -Real.log (250000000000 / 448340603059) ∧
    -Real.log (250000000000 / 448340603059) ≤ (584092301 / 1000000000) := by
  have h := checkLog_sound (w := (198340603059 / 698340603059)) (n := 12)
    (lo := (5840923 / 10000000)) (hi := (584092301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448340603059 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448340603059 / 250000000000) = 1/(250000000000 / 448340603059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5840923 / 10000000) (584092301 / 1000000000) (Real.log (448340603059 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (448340603059 / 250000000000) = -Real.log (250000000000 / 448340603059) := by
    rw [show ((448340603059 / 250000000000) : ℝ) = ((250000000000 / 448340603059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (585017003 / 1000000000) ≤ -Real.log (250000000000 / 448755376923) ∧
    -Real.log (250000000000 / 448755376923) ≤ (146254251 / 250000000) := by
  have h := checkLog_sound (w := (198755376923 / 698755376923)) (n := 12)
    (lo := (585017003 / 1000000000)) (hi := (146254251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448755376923 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448755376923 / 250000000000) = 1/(250000000000 / 448755376923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (585017003 / 1000000000) (146254251 / 250000000) (Real.log (448755376923 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (448755376923 / 250000000000) = -Real.log (250000000000 / 448755376923) := by
    rw [show ((448755376923 / 250000000000) : ℝ) = ((250000000000 / 448755376923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (416767571 / 1000000000) ≤ -Real.log (250000000000 / 379262466633) ∧
    -Real.log (250000000000 / 379262466633) ≤ (104191893 / 250000000) := by
  have h := checkLog_sound (w := (129262466633 / 629262466633)) (n := 12)
    (lo := (416767571 / 1000000000)) (hi := (104191893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379262466633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379262466633 / 250000000000) = 1/(250000000000 / 379262466633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (416767571 / 1000000000) (104191893 / 250000000) (Real.log (379262466633 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (379262466633 / 250000000000) = -Real.log (250000000000 / 379262466633) := by
    rw [show ((379262466633 / 250000000000) : ℝ) = ((250000000000 / 379262466633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41743999 / 100000000) ≤ -Real.log (500000000000 / 759035151003) ∧
    -Real.log (500000000000 / 759035151003) ≤ (417439991 / 1000000000) := by
  have h := checkLog_sound (w := (259035151003 / 1259035151003)) (n := 12)
    (lo := (41743999 / 100000000)) (hi := (417439991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759035151003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759035151003 / 500000000000) = 1/(500000000000 / 759035151003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41743999 / 100000000) (417439991 / 1000000000) (Real.log (759035151003 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (759035151003 / 500000000000) = -Real.log (500000000000 / 759035151003) := by
    rw [show ((759035151003 / 500000000000) : ℝ) = ((500000000000 / 759035151003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21625679 / 500000000) ≤ -Real.log (957670640919 / 1000000000000) ∧
    -Real.log (957670640919 / 1000000000000) ≤ (43251359 / 1000000000) := by
  have h := checkLog_sound (w := (42329359081 / 1957670640919)) (n := 12)
    (lo := (21625679 / 500000000)) (hi := (43251359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957670640919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957670640919) = 1/(957670640919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-43251359 / 1000000000) (-21625679 / 500000000) (Real.log (957670640919 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21556561 / 500000000) ≤ -Real.log (957803034439 / 1000000000000) ∧
    -Real.log (957803034439 / 1000000000000) ≤ (43113123 / 1000000000) := by
  have h := checkLog_sound (w := (42196965561 / 1957803034439)) (n := 12)
    (lo := (21556561 / 500000000)) (hi := (43113123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957803034439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957803034439) = 1/(957803034439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-43113123 / 1000000000) (-21556561 / 500000000) (Real.log (957803034439 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell254

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell255Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell255
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

theorem reflection_log_1_neg : (84118059 / 250000000) ≤ -Real.log (5 / 7) ∧
    -Real.log (5 / 7) ≤ (336472237 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6)) (n := 12)
    (lo := (84118059 / 250000000)) (hi := (336472237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7 / 5) = 1/(5 / 7) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84118059 / 250000000) (336472237 / 1000000000) (Real.log (7 / 5)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7 / 5) = -Real.log (5 / 7) := by
    rw [show ((7 / 5) : ℝ) = ((5 / 7) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (510825623 / 1000000000) ≤ -Real.log (3 / 5) ∧
    -Real.log (3 / 5) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 3) = 1/(3 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63853203 / 125000000) (-510825623 / 1000000000) (Real.log (3 / 5)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (168026811 / 500000000) ≤ -Real.log (1024 / 1433) ∧
    -Real.log (1024 / 1433) ≤ (336053623 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2457)) (n := 12)
    (lo := (168026811 / 500000000)) (hi := (336053623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433 / 1024) = 1/(1024 / 1433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (168026811 / 500000000) (336053623 / 1000000000) (Real.log (1433 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1433 / 1024) = -Real.log (1024 / 1433) := by
    rw [show ((1433 / 1024) : ℝ) = ((1024 / 1433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (509849537 / 1000000000) ≤ -Real.log (615 / 1024) ∧
    -Real.log (615 / 1024) ≤ (254924769 / 500000000) := by
  have h := checkLog_sound (w := (409 / 1639)) (n := 12)
    (lo := (509849537 / 1000000000)) (hi := (254924769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 615) = 1/(615 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-254924769 / 500000000) (-509849537 / 1000000000) (Real.log (615 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62580901 / 250000000) ≤ -Real.log (1000000 / 1284441) ∧
    -Real.log (1000000 / 1284441) ≤ (50064721 / 200000000) := by
  have h := checkLog_sound (w := (284441 / 2284441)) (n := 12)
    (lo := (62580901 / 250000000)) (hi := (50064721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1284441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1284441 / 1000000) = 1/(1000000 / 1284441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62580901 / 250000000) (50064721 / 200000000) (Real.log (1284441 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1284441 / 1000000) = -Real.log (1000000 / 1284441) := by
    rw [show ((1284441 / 1000000) : ℝ) = ((1000000 / 1284441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (334691223 / 1000000000) ≤ -Real.log (715559 / 1000000) ∧
    -Real.log (715559 / 1000000) ≤ (41836403 / 125000000) := by
  have h := checkLog_sound (w := (284441 / 1715559)) (n := 12)
    (lo := (334691223 / 1000000000)) (hi := (41836403 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 715559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 715559) = 1/(715559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41836403 / 125000000) (-334691223 / 1000000000) (Real.log (715559 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7832951 / 31250000) ≤ -Real.log (500000 / 642433) ∧
    -Real.log (500000 / 642433) ≤ (250654433 / 1000000000) := by
  have h := checkLog_sound (w := (142433 / 1142433)) (n := 12)
    (lo := (7832951 / 31250000)) (hi := (250654433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642433 / 500000) = 1/(500000 / 642433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7832951 / 31250000) (250654433 / 1000000000) (Real.log (642433 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (642433 / 500000) = -Real.log (500000 / 642433) := by
    rw [show ((642433 / 500000) : ℝ) = ((500000 / 642433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (335285341 / 1000000000) ≤ -Real.log (357567 / 500000) ∧
    -Real.log (357567 / 500000) ≤ (167642671 / 500000000) := by
  have h := checkLog_sound (w := (142433 / 857567)) (n := 12)
    (lo := (335285341 / 1000000000)) (hi := (167642671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357567) = 1/(357567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-167642671 / 500000000) (-335285341 / 1000000000) (Real.log (357567 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (93546743 / 500000000) ≤ -Real.log (50000 / 60287) ∧
    -Real.log (50000 / 60287) ≤ (187093487 / 1000000000) := by
  have h := checkLog_sound (w := (10287 / 110287)) (n := 12)
    (lo := (93546743 / 500000000)) (hi := (187093487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60287 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60287 / 50000) = 1/(50000 / 60287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (93546743 / 500000000) (187093487 / 1000000000) (Real.log (60287 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (60287 / 50000) = -Real.log (50000 / 60287) := by
    rw [show ((60287 / 50000) : ℝ) = ((50000 / 60287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46068883 / 200000000) ≤ -Real.log (39713 / 50000) ∧
    -Real.log (39713 / 50000) ≤ (7198263 / 31250000) := by
  have h := checkLog_sound (w := (10287 / 89713)) (n := 12)
    (lo := (46068883 / 200000000)) (hi := (7198263 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39713) = 1/(39713 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7198263 / 31250000) (-46068883 / 200000000) (Real.log (39713 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (187359677 / 1000000000) ≤ -Real.log (1000000 / 1206061) ∧
    -Real.log (1000000 / 1206061) ≤ (93679839 / 500000000) := by
  have h := checkLog_sound (w := (206061 / 2206061)) (n := 12)
    (lo := (187359677 / 1000000000)) (hi := (93679839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206061 / 1000000) = 1/(1000000 / 1206061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (187359677 / 1000000000) (93679839 / 500000000) (Real.log (1206061 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1206061 / 1000000) = -Real.log (1000000 / 1206061) := by
    rw [show ((1206061 / 1000000) : ℝ) = ((1000000 / 1206061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (115374323 / 500000000) ≤ -Real.log (793939 / 1000000) ∧
    -Real.log (793939 / 1000000) ≤ (230748647 / 1000000000) := by
  have h := checkLog_sound (w := (206061 / 1793939)) (n := 12)
    (lo := (115374323 / 500000000)) (hi := (230748647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793939) = 1/(793939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-230748647 / 1000000000) (-115374323 / 500000000) (Real.log (793939 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (845903159 / 1000000000) ≤ -Real.log (250000000000 / 582520325203) ∧
    -Real.log (250000000000 / 582520325203) ≤ (845903161 / 1000000000) := by
  have h := checkLog_sound (w := (82520325203 / 1082520325203)) (n := 12)
    (lo := (152755979 / 1000000000)) (hi := (7637799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582520325203 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(582520325203 / 500000000000) = 1/(250000000000 / 582520325203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (845903159 / 1000000000) (845903161 / 1000000000) (Real.log (582520325203 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (582520325203 / 250000000000) = -Real.log (250000000000 / 582520325203) := by
    rw [show ((582520325203 / 250000000000) : ℝ) = ((250000000000 / 582520325203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (847297859 / 1000000000) ≤ -Real.log (500000000000 / 1166666666667) ∧
    -Real.log (500000000000 / 1166666666667) ≤ (847297861 / 1000000000) := by
  have h := checkLog_sound (w := (166666666667 / 2166666666667)) (n := 12)
    (lo := (154150679 / 1000000000)) (hi := (3853767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166666666667 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1166666666667 / 1000000000000) = 1/(500000000000 / 1166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (847297859 / 1000000000) (847297861 / 1000000000) (Real.log (1166666666667 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1166666666667 / 500000000000) = -Real.log (500000000000 / 1166666666667) := by
    rw [show ((1166666666667 / 500000000000) : ℝ) = ((500000000000 / 1166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (585014827 / 1000000000) ≤ -Real.log (500000000000 / 897508800811) ∧
    -Real.log (500000000000 / 897508800811) ≤ (146253707 / 250000000) := by
  have h := checkLog_sound (w := (397508800811 / 1397508800811)) (n := 12)
    (lo := (585014827 / 1000000000)) (hi := (146253707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897508800811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897508800811 / 500000000000) = 1/(500000000000 / 897508800811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (585014827 / 1000000000) (146253707 / 250000000) (Real.log (897508800811 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (897508800811 / 500000000000) = -Real.log (500000000000 / 897508800811) := by
    rw [show ((897508800811 / 500000000000) : ℝ) = ((500000000000 / 897508800811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (292969887 / 500000000) ≤ -Real.log (50000000000 / 89833933221) ∧
    -Real.log (50000000000 / 89833933221) ≤ (23437591 / 40000000) := by
  have h := checkLog_sound (w := (39833933221 / 139833933221)) (n := 12)
    (lo := (292969887 / 500000000)) (hi := (23437591 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89833933221 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89833933221 / 50000000000) = 1/(50000000000 / 89833933221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (292969887 / 500000000) (23437591 / 40000000) (Real.log (89833933221 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (89833933221 / 50000000000) = -Real.log (50000000000 / 89833933221) := by
    rw [show ((89833933221 / 50000000000) : ℝ) = ((50000000000 / 89833933221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (417437901 / 1000000000) ≤ -Real.log (250000000000 / 379516782917) ∧
    -Real.log (250000000000 / 379516782917) ≤ (208718951 / 500000000) := by
  have h := checkLog_sound (w := (129516782917 / 629516782917)) (n := 12)
    (lo := (417437901 / 1000000000)) (hi := (208718951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379516782917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379516782917 / 250000000000) = 1/(250000000000 / 379516782917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (417437901 / 1000000000) (208718951 / 500000000) (Real.log (379516782917 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (379516782917 / 250000000000) = -Real.log (250000000000 / 379516782917) := by
    rw [show ((379516782917 / 250000000000) : ℝ) = ((250000000000 / 379516782917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (104527081 / 250000000) ≤ -Real.log (500000000000 / 759542609697) ∧
    -Real.log (500000000000 / 759542609697) ≤ (16724333 / 40000000) := by
  have h := checkLog_sound (w := (259542609697 / 1259542609697)) (n := 12)
    (lo := (104527081 / 250000000)) (hi := (16724333 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759542609697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759542609697 / 500000000000) = 1/(500000000000 / 759542609697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (104527081 / 250000000) (16724333 / 40000000) (Real.log (759542609697 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (759542609697 / 500000000000) = -Real.log (500000000000 / 759542609697) := by
    rw [show ((759542609697 / 500000000000) : ℝ) = ((500000000000 / 759542609697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43388969 / 1000000000) ≤ -Real.log (957538864279 / 1000000000000) ∧
    -Real.log (957538864279 / 1000000000000) ≤ (4338897 / 100000000) := by
  have h := checkLog_sound (w := (42461135721 / 1957538864279)) (n := 12)
    (lo := (43388969 / 1000000000)) (hi := (4338897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957538864279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957538864279) = 1/(957538864279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4338897 / 100000000) (-43388969 / 1000000000) (Real.log (957538864279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (43250929 / 1000000000) ≤ -Real.log (2394177631 / 2500000000) ∧
    -Real.log (2394177631 / 2500000000) ≤ (4325093 / 100000000) := by
  have h := checkLog_sound (w := (105822369 / 4894177631)) (n := 12)
    (lo := (43250929 / 1000000000)) (hi := (4325093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2394177631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2394177631) = 1/(2394177631 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4325093 / 100000000) (-43250929 / 1000000000) (Real.log (2394177631 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell255

end


