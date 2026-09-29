-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0003__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0003__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T05:39:43.572774+00:00
-- url     : https://prove2.me/theorems/c2dcff29-80db-4210-89d3-c7c5784b5714
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0003 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0004, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0003 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0004, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0005)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0003 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0004, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0005)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0003 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0004, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0005) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0003 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0004, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0005).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0003 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_192_neg : (82142597 / 500000000) ≤ -Real.log (1697 / 2000) ∧
    -Real.log (1697 / 2000) ≤ (32857039 / 200000000) := by
  have h := checkLog_sound (w := (303 / 3697)) (n := 12)
    (lo := (82142597 / 500000000)) (hi := (32857039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1697) = 1/(1697 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_192 : Bounds (-32857039 / 200000000) (-82142597 / 500000000) (Real.log (1697 / 2000)) := by
  have h := reflection_log_192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_193_neg : (2367 / 15625000) ≤ -Real.log (2000000 / 2000303) ∧
    -Real.log (2000000 / 2000303) ≤ (151489 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 4000303)) (n := 12)
    (lo := (2367 / 15625000)) (hi := (151489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000303 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000303 / 2000000) = 1/(2000000 / 2000303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_193 : Bounds (2367 / 15625000) (151489 / 1000000000) (Real.log (2000303 / 2000000)) := by
  have h := reflection_log_193_neg
  have he : Real.log (2000303 / 2000000) = -Real.log (2000000 / 2000303) := by
    rw [show ((2000303 / 2000000) : ℝ) = ((2000000 / 2000303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_194_neg : (151511 / 1000000000) ≤ -Real.log (1999697 / 2000000) ∧
    -Real.log (1999697 / 2000000) ≤ (18939 / 125000000) := by
  have h := checkLog_sound (w := (303 / 3999697)) (n := 12)
    (lo := (151511 / 1000000000)) (hi := (18939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999697) = 1/(1999697 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_194 : Bounds (-18939 / 125000000) (-151511 / 1000000000) (Real.log (1999697 / 2000000)) := by
  have h := reflection_log_194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_195_neg : (73382423 / 1000000000) ≤ -Real.log (500000 / 538071) ∧
    -Real.log (500000 / 538071) ≤ (9172803 / 125000000) := by
  have h := checkLog_sound (w := (38071 / 1038071)) (n := 12)
    (lo := (73382423 / 1000000000)) (hi := (9172803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538071 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538071 / 500000) = 1/(500000 / 538071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_195 : Bounds (73382423 / 1000000000) (9172803 / 125000000) (Real.log (538071 / 500000)) := by
  have h := reflection_log_195_neg
  have he : Real.log (538071 / 500000) = -Real.log (500000 / 538071) := by
    rw [show ((538071 / 500000) : ℝ) = ((500000 / 538071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_196_neg : (39598449 / 500000000) ≤ -Real.log (461929 / 500000) ∧
    -Real.log (461929 / 500000) ≤ (79196899 / 1000000000) := by
  have h := checkLog_sound (w := (38071 / 961929)) (n := 12)
    (lo := (39598449 / 500000000)) (hi := (79196899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461929) = 1/(461929 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_196 : Bounds (-79196899 / 1000000000) (-39598449 / 500000000) (Real.log (461929 / 500000)) := by
  have h := reflection_log_196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_197_neg : (232579 / 40000000) ≤ -Real.log (248550598959 / 250000000000) ∧
    -Real.log (248550598959 / 250000000000) ≤ (1453619 / 250000000) := by
  have h := checkLog_sound (w := (1449401041 / 498550598959)) (n := 12)
    (lo := (232579 / 40000000)) (hi := (1453619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248550598959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248550598959) = 1/(248550598959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_197 : Bounds (-1453619 / 250000000) (-232579 / 40000000) (Real.log (248550598959 / 250000000000)) := by
  have h := reflection_log_197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_198_neg : (1902137 / 12500000) ≤ -Real.log (100000000000 / 116435927931) ∧
    -Real.log (100000000000 / 116435927931) ≤ (152170961 / 1000000000) := by
  have h := checkLog_sound (w := (16435927931 / 216435927931)) (n := 12)
    (lo := (1902137 / 12500000)) (hi := (152170961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116435927931 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116435927931 / 100000000000) = 1/(100000000000 / 116435927931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_198 : Bounds (1902137 / 12500000) (152170961 / 1000000000) (Real.log (116435927931 / 100000000000)) := by
  have h := reflection_log_198_neg
  have he : Real.log (116435927931 / 100000000000) = -Real.log (100000000000 / 116435927931) := by
    rw [show ((116435927931 / 100000000000) : ℝ) = ((100000000000 / 116435927931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_199_neg : (76289661 / 500000000) ≤ -Real.log (500000000000 / 582417427787) ∧
    -Real.log (500000000000 / 582417427787) ≤ (152579323 / 1000000000) := by
  have h := checkLog_sound (w := (82417427787 / 1082417427787)) (n := 12)
    (lo := (76289661 / 500000000)) (hi := (152579323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582417427787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582417427787 / 500000000000) = 1/(500000000000 / 582417427787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_199 : Bounds (76289661 / 500000000) (152579323 / 1000000000) (Real.log (582417427787 / 500000000000)) := by
  have h := reflection_log_199_neg
  have he : Real.log (582417427787 / 500000000000) = -Real.log (500000000000 / 582417427787) := by
    rw [show ((582417427787 / 500000000000) : ℝ) = ((500000000000 / 582417427787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_200_neg : (305145939 / 1000000000) ≤ -Real.log (31250000000 / 42400718831) ∧
    -Real.log (31250000000 / 42400718831) ≤ (15257297 / 50000000) := by
  have h := checkLog_sound (w := (11150718831 / 73650718831)) (n := 12)
    (lo := (305145939 / 1000000000)) (hi := (15257297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42400718831 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42400718831 / 31250000000) = 1/(31250000000 / 42400718831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_200 : Bounds (305145939 / 1000000000) (15257297 / 50000000) (Real.log (42400718831 / 31250000000)) := by
  have h := reflection_log_200_neg
  have he : Real.log (42400718831 / 31250000000) = -Real.log (31250000000 / 42400718831) := by
    rw [show ((42400718831 / 31250000000) : ℝ) = ((31250000000 / 42400718831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_201_neg : (152675317 / 500000000) ≤ -Real.log (500000000000 / 678550383029) ∧
    -Real.log (500000000000 / 678550383029) ≤ (61070127 / 200000000) := by
  have h := checkLog_sound (w := (178550383029 / 1178550383029)) (n := 12)
    (lo := (152675317 / 500000000)) (hi := (61070127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678550383029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678550383029 / 500000000000) = 1/(500000000000 / 678550383029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_201 : Bounds (152675317 / 500000000) (61070127 / 200000000) (Real.log (678550383029 / 500000000000)) := by
  have h := reflection_log_201_neg
  have he : Real.log (678550383029 / 500000000000) = -Real.log (500000000000 / 678550383029) := by
    rw [show ((678550383029 / 500000000000) : ℝ) = ((500000000000 / 678550383029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_202_neg : (141152279 / 1000000000) ≤ -Real.log (2500 / 2879) ∧
    -Real.log (2500 / 2879) ≤ (3528807 / 25000000) := by
  have h := checkLog_sound (w := (379 / 5379)) (n := 12)
    (lo := (141152279 / 1000000000)) (hi := (3528807 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2879 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2879 / 2500) = 1/(2500 / 2879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_202 : Bounds (141152279 / 1000000000) (3528807 / 25000000) (Real.log (2879 / 2500)) := by
  have h := reflection_log_202_neg
  have he : Real.log (2879 / 2500) = -Real.log (2500 / 2879) := by
    rw [show ((2879 / 2500) : ℝ) = ((2500 / 2879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_203_neg : (10275191 / 62500000) ≤ -Real.log (2121 / 2500) ∧
    -Real.log (2121 / 2500) ≤ (164403057 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 4621)) (n := 12)
    (lo := (10275191 / 62500000)) (hi := (164403057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2121) = 1/(2121 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_203 : Bounds (-164403057 / 1000000000) (-10275191 / 62500000) (Real.log (2121 / 2500)) := by
  have h := reflection_log_203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_204_neg : (37897 / 250000000) ≤ -Real.log (2500000 / 2500379) ∧
    -Real.log (2500000 / 2500379) ≤ (151589 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 5000379)) (n := 12)
    (lo := (37897 / 250000000)) (hi := (151589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500379 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500379 / 2500000) = 1/(2500000 / 2500379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_204 : Bounds (37897 / 250000000) (151589 / 1000000000) (Real.log (2500379 / 2500000)) := by
  have h := reflection_log_204_neg
  have he : Real.log (2500379 / 2500000) = -Real.log (2500000 / 2500379) := by
    rw [show ((2500379 / 2500000) : ℝ) = ((2500000 / 2500379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_205_neg : (151611 / 1000000000) ≤ -Real.log (2499621 / 2500000) ∧
    -Real.log (2499621 / 2500000) ≤ (37903 / 250000000) := by
  have h := checkLog_sound (w := (379 / 4999621)) (n := 12)
    (lo := (151611 / 1000000000)) (hi := (37903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499621) = 1/(2499621 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_205 : Bounds (-37903 / 250000000) (-151611 / 1000000000) (Real.log (2499621 / 2500000)) := by
  have h := reflection_log_205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_206_neg : (18357221 / 250000000) ≤ -Real.log (31250 / 33631) ∧
    -Real.log (31250 / 33631) ≤ (14685777 / 200000000) := by
  have h := checkLog_sound (w := (2381 / 64881)) (n := 12)
    (lo := (18357221 / 250000000)) (hi := (14685777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33631 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33631 / 31250) = 1/(31250 / 33631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_206 : Bounds (18357221 / 250000000) (14685777 / 200000000) (Real.log (33631 / 31250)) := by
  have h := reflection_log_206_neg
  have he : Real.log (33631 / 31250) = -Real.log (31250 / 33631) := by
    rw [show ((33631 / 31250) : ℝ) = ((31250 / 33631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_207_neg : (79251021 / 1000000000) ≤ -Real.log (28869 / 31250) ∧
    -Real.log (28869 / 31250) ≤ (39625511 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 60119)) (n := 12)
    (lo := (79251021 / 1000000000)) (hi := (39625511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28869) = 1/(28869 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_207 : Bounds (-39625511 / 500000000) (-79251021 / 1000000000) (Real.log (28869 / 31250)) := by
  have h := reflection_log_207_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_208_neg : (727767 / 125000000) ≤ -Real.log (970893339 / 976562500) ∧
    -Real.log (970893339 / 976562500) ≤ (5822137 / 1000000000) := by
  have h := checkLog_sound (w := (5669161 / 1947455839)) (n := 12)
    (lo := (727767 / 125000000)) (hi := (5822137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 970893339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 970893339) = 1/(970893339 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_208 : Bounds (-5822137 / 1000000000) (-727767 / 125000000) (Real.log (970893339 / 976562500)) := by
  have h := reflection_log_208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_209_neg : (9517097 / 62500000) ≤ -Real.log (500000000000 / 582239369703) ∧
    -Real.log (500000000000 / 582239369703) ≤ (152273553 / 1000000000) := by
  have h := checkLog_sound (w := (82239369703 / 1082239369703)) (n := 12)
    (lo := (9517097 / 62500000)) (hi := (152273553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582239369703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582239369703 / 500000000000) = 1/(500000000000 / 582239369703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_209 : Bounds (9517097 / 62500000) (152273553 / 1000000000) (Real.log (582239369703 / 500000000000)) := by
  have h := reflection_log_209_neg
  have he : Real.log (582239369703 / 500000000000) = -Real.log (500000000000 / 582239369703) := by
    rw [show ((582239369703 / 500000000000) : ℝ) = ((500000000000 / 582239369703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_210_neg : (30535981 / 200000000) ≤ -Real.log (125000000000 / 145619003083) ∧
    -Real.log (125000000000 / 145619003083) ≤ (76339953 / 500000000) := by
  have h := checkLog_sound (w := (20619003083 / 270619003083)) (n := 12)
    (lo := (30535981 / 200000000)) (hi := (76339953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145619003083 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145619003083 / 125000000000) = 1/(125000000000 / 145619003083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_210 : Bounds (30535981 / 200000000) (76339953 / 500000000) (Real.log (145619003083 / 125000000000)) := by
  have h := reflection_log_210_neg
  have he : Real.log (145619003083 / 125000000000) = -Real.log (125000000000 / 145619003083) := by
    rw [show ((145619003083 / 125000000000) : ℝ) = ((125000000000 / 145619003083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_211_neg : (152675317 / 500000000) ≤ -Real.log (125000000000 / 169637595757) ∧
    -Real.log (125000000000 / 169637595757) ≤ (61070127 / 200000000) := by
  have h := checkLog_sound (w := (44637595757 / 294637595757)) (n := 12)
    (lo := (152675317 / 500000000)) (hi := (61070127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169637595757 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169637595757 / 125000000000) = 1/(125000000000 / 169637595757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_211 : Bounds (152675317 / 500000000) (61070127 / 200000000) (Real.log (169637595757 / 125000000000)) := by
  have h := reflection_log_211_neg
  have he : Real.log (169637595757 / 125000000000) = -Real.log (125000000000 / 169637595757) := by
    rw [show ((169637595757 / 125000000000) : ℝ) = ((125000000000 / 169637595757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_212_neg : (38194417 / 125000000) ≤ -Real.log (250000000000 / 339344648751) ∧
    -Real.log (250000000000 / 339344648751) ≤ (305555337 / 1000000000) := by
  have h := checkLog_sound (w := (89344648751 / 589344648751)) (n := 12)
    (lo := (38194417 / 125000000)) (hi := (305555337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339344648751 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339344648751 / 250000000000) = 1/(250000000000 / 339344648751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_212 : Bounds (38194417 / 125000000) (305555337 / 1000000000) (Real.log (339344648751 / 250000000000)) := by
  have h := reflection_log_212_neg
  have he : Real.log (339344648751 / 250000000000) = -Real.log (250000000000 / 339344648751) := by
    rw [show ((339344648751 / 250000000000) : ℝ) = ((250000000000 / 339344648751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_213_neg : (141239111 / 1000000000) ≤ -Real.log (10000 / 11517) ∧
    -Real.log (10000 / 11517) ≤ (17654889 / 125000000) := by
  have h := checkLog_sound (w := (1517 / 21517)) (n := 12)
    (lo := (141239111 / 1000000000)) (hi := (17654889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11517 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11517 / 10000) = 1/(10000 / 11517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_213 : Bounds (141239111 / 1000000000) (17654889 / 125000000) (Real.log (11517 / 10000)) := by
  have h := reflection_log_213_neg
  have he : Real.log (11517 / 10000) = -Real.log (10000 / 11517) := by
    rw [show ((11517 / 10000) : ℝ) = ((10000 / 11517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_214_neg : (41130233 / 250000000) ≤ -Real.log (8483 / 10000) ∧
    -Real.log (8483 / 10000) ≤ (164520933 / 1000000000) := by
  have h := checkLog_sound (w := (1517 / 18483)) (n := 12)
    (lo := (41130233 / 250000000)) (hi := (164520933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8483) = 1/(8483 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_214 : Bounds (-164520933 / 1000000000) (-41130233 / 250000000) (Real.log (8483 / 10000)) := by
  have h := reflection_log_214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_215_neg : (18961 / 125000000) ≤ -Real.log (10000000 / 10001517) ∧
    -Real.log (10000000 / 10001517) ≤ (151689 / 1000000000) := by
  have h := checkLog_sound (w := (1517 / 20001517)) (n := 12)
    (lo := (18961 / 125000000)) (hi := (151689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001517 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001517 / 10000000) = 1/(10000000 / 10001517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_215 : Bounds (18961 / 125000000) (151689 / 1000000000) (Real.log (10001517 / 10000000)) := by
  have h := reflection_log_215_neg
  have he : Real.log (10001517 / 10000000) = -Real.log (10000000 / 10001517) := by
    rw [show ((10001517 / 10000000) : ℝ) = ((10000000 / 10001517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_216_neg : (151711 / 1000000000) ≤ -Real.log (9998483 / 10000000) ∧
    -Real.log (9998483 / 10000000) ≤ (4741 / 31250000) := by
  have h := checkLog_sound (w := (1517 / 19998483)) (n := 12)
    (lo := (151711 / 1000000000)) (hi := (4741 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998483) = 1/(9998483 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_216 : Bounds (-4741 / 31250000) (-151711 / 1000000000) (Real.log (9998483 / 10000000)) := by
  have h := reflection_log_216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_217_neg : (4592267 / 62500000) ≤ -Real.log (1000000 / 1076243) ∧
    -Real.log (1000000 / 1076243) ≤ (73476273 / 1000000000) := by
  have h := checkLog_sound (w := (76243 / 2076243)) (n := 12)
    (lo := (4592267 / 62500000)) (hi := (73476273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076243 / 1000000) = 1/(1000000 / 1076243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_217 : Bounds (4592267 / 62500000) (73476273 / 1000000000) (Real.log (1076243 / 1000000)) := by
  have h := reflection_log_217_neg
  have he : Real.log (1076243 / 1000000) = -Real.log (1000000 / 1076243) := by
    rw [show ((1076243 / 1000000) : ℝ) = ((1000000 / 1076243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_218_neg : (19826557 / 250000000) ≤ -Real.log (923757 / 1000000) ∧
    -Real.log (923757 / 1000000) ≤ (79306229 / 1000000000) := by
  have h := checkLog_sound (w := (76243 / 1923757)) (n := 12)
    (lo := (19826557 / 250000000)) (hi := (79306229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923757) = 1/(923757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_218 : Bounds (-79306229 / 1000000000) (-19826557 / 250000000) (Real.log (923757 / 1000000)) := by
  have h := reflection_log_218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_219_neg : (1457489 / 250000000) ≤ -Real.log (994187004951 / 1000000000000) ∧
    -Real.log (994187004951 / 1000000000000) ≤ (5829957 / 1000000000) := by
  have h := checkLog_sound (w := (5812995049 / 1994187004951)) (n := 12)
    (lo := (1457489 / 250000000)) (hi := (5829957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994187004951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994187004951) = 1/(994187004951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_219 : Bounds (-5829957 / 1000000000) (-1457489 / 250000000) (Real.log (994187004951 / 1000000000000)) := by
  have h := reflection_log_219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_220_neg : (76187067 / 500000000) ≤ -Real.log (20000000000 / 23291917399) ∧
    -Real.log (20000000000 / 23291917399) ≤ (30474827 / 200000000) := by
  have h := checkLog_sound (w := (3291917399 / 43291917399)) (n := 12)
    (lo := (76187067 / 500000000)) (hi := (30474827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23291917399 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23291917399 / 20000000000) = 1/(20000000000 / 23291917399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_220 : Bounds (76187067 / 500000000) (30474827 / 200000000) (Real.log (23291917399 / 20000000000)) := by
  have h := reflection_log_220_neg
  have he : Real.log (23291917399 / 20000000000) = -Real.log (20000000000 / 23291917399) := by
    rw [show ((23291917399 / 20000000000) : ℝ) = ((20000000000 / 23291917399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_221_neg : (152782501 / 1000000000) ≤ -Real.log (250000000000 / 291267887551) ∧
    -Real.log (250000000000 / 291267887551) ≤ (76391251 / 500000000) := by
  have h := checkLog_sound (w := (41267887551 / 541267887551)) (n := 12)
    (lo := (152782501 / 1000000000)) (hi := (76391251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291267887551 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291267887551 / 250000000000) = 1/(250000000000 / 291267887551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_221 : Bounds (152782501 / 1000000000) (76391251 / 500000000) (Real.log (291267887551 / 250000000000)) := by
  have h := reflection_log_221_neg
  have he : Real.log (291267887551 / 250000000000) = -Real.log (250000000000 / 291267887551) := by
    rw [show ((291267887551 / 250000000000) : ℝ) = ((250000000000 / 291267887551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_222_neg : (38194417 / 125000000) ≤ -Real.log (500000000000 / 678689297501) ∧
    -Real.log (500000000000 / 678689297501) ≤ (305555337 / 1000000000) := by
  have h := checkLog_sound (w := (178689297501 / 1178689297501)) (n := 12)
    (lo := (38194417 / 125000000)) (hi := (305555337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678689297501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678689297501 / 500000000000) = 1/(500000000000 / 678689297501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_222 : Bounds (38194417 / 125000000) (305555337 / 1000000000) (Real.log (678689297501 / 500000000000)) := by
  have h := reflection_log_222_neg
  have he : Real.log (678689297501 / 500000000000) = -Real.log (500000000000 / 678689297501) := by
    rw [show ((678689297501 / 500000000000) : ℝ) = ((500000000000 / 678689297501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_223_neg : (305760043 / 1000000000) ≤ -Real.log (20000000000 / 27153129789) ∧
    -Real.log (20000000000 / 27153129789) ≤ (76440011 / 250000000) := by
  have h := checkLog_sound (w := (7153129789 / 47153129789)) (n := 12)
    (lo := (305760043 / 1000000000)) (hi := (76440011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27153129789 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27153129789 / 20000000000) = 1/(20000000000 / 27153129789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_223 : Bounds (305760043 / 1000000000) (76440011 / 250000000) (Real.log (27153129789 / 20000000000)) := by
  have h := reflection_log_223_neg
  have he : Real.log (27153129789 / 20000000000) = -Real.log (20000000000 / 27153129789) := by
    rw [show ((27153129789 / 20000000000) : ℝ) = ((20000000000 / 27153129789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_224_neg : (8832871 / 62500000) ≤ -Real.log (5000 / 5759) ∧
    -Real.log (5000 / 5759) ≤ (141325937 / 1000000000) := by
  have h := checkLog_sound (w := (759 / 10759)) (n := 12)
    (lo := (8832871 / 62500000)) (hi := (141325937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5759 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5759 / 5000) = 1/(5000 / 5759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_224 : Bounds (8832871 / 62500000) (141325937 / 1000000000) (Real.log (5759 / 5000)) := by
  have h := reflection_log_224_neg
  have he : Real.log (5759 / 5000) = -Real.log (5000 / 5759) := by
    rw [show ((5759 / 5000) : ℝ) = ((5000 / 5759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_225_neg : (164638821 / 1000000000) ≤ -Real.log (4241 / 5000) ∧
    -Real.log (4241 / 5000) ≤ (82319411 / 500000000) := by
  have h := checkLog_sound (w := (759 / 9241)) (n := 12)
    (lo := (164638821 / 1000000000)) (hi := (82319411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4241) = 1/(4241 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_225 : Bounds (-82319411 / 500000000) (-164638821 / 1000000000) (Real.log (4241 / 5000)) := by
  have h := reflection_log_225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_226_neg : (37947 / 250000000) ≤ -Real.log (5000000 / 5000759) ∧
    -Real.log (5000000 / 5000759) ≤ (151789 / 1000000000) := by
  have h := checkLog_sound (w := (759 / 10000759)) (n := 12)
    (lo := (37947 / 250000000)) (hi := (151789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000759 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000759 / 5000000) = 1/(5000000 / 5000759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_226 : Bounds (37947 / 250000000) (151789 / 1000000000) (Real.log (5000759 / 5000000)) := by
  have h := reflection_log_226_neg
  have he : Real.log (5000759 / 5000000) = -Real.log (5000000 / 5000759) := by
    rw [show ((5000759 / 5000000) : ℝ) = ((5000000 / 5000759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_227_neg : (151811 / 1000000000) ≤ -Real.log (4999241 / 5000000) ∧
    -Real.log (4999241 / 5000000) ≤ (37953 / 250000000) := by
  have h := checkLog_sound (w := (759 / 9999241)) (n := 12)
    (lo := (151811 / 1000000000)) (hi := (37953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999241) = 1/(4999241 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_227 : Bounds (-37953 / 250000000) (-151811 / 1000000000) (Real.log (4999241 / 5000000)) := by
  have h := reflection_log_227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_228_neg : (36761829 / 500000000) ≤ -Real.log (500000 / 538147) ∧
    -Real.log (500000 / 538147) ≤ (73523659 / 1000000000) := by
  have h := checkLog_sound (w := (38147 / 1038147)) (n := 12)
    (lo := (36761829 / 500000000)) (hi := (73523659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538147 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538147 / 500000) = 1/(500000 / 538147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_228 : Bounds (36761829 / 500000000) (73523659 / 1000000000) (Real.log (538147 / 500000)) := by
  have h := reflection_log_228_neg
  have he : Real.log (538147 / 500000) = -Real.log (500000 / 538147) := by
    rw [show ((538147 / 500000) : ℝ) = ((500000 / 538147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_229_neg : (79361439 / 1000000000) ≤ -Real.log (461853 / 500000) ∧
    -Real.log (461853 / 500000) ≤ (496009 / 6250000) := by
  have h := checkLog_sound (w := (38147 / 961853)) (n := 12)
    (lo := (79361439 / 1000000000)) (hi := (496009 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461853) = 1/(461853 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_229 : Bounds (-496009 / 6250000) (-79361439 / 1000000000) (Real.log (461853 / 500000)) := by
  have h := reflection_log_229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_230_neg : (5837781 / 1000000000) ≤ -Real.log (248544806391 / 250000000000) ∧
    -Real.log (248544806391 / 250000000000) ≤ (2918891 / 500000000) := by
  have h := checkLog_sound (w := (1455193609 / 498544806391)) (n := 12)
    (lo := (5837781 / 1000000000)) (hi := (2918891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248544806391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248544806391) = 1/(248544806391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_230 : Bounds (-2918891 / 500000000) (-5837781 / 1000000000) (Real.log (248544806391 / 250000000000)) := by
  have h := reflection_log_230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_231_neg : (152476727 / 1000000000) ≤ -Real.log (500000000000 / 582357678083) ∧
    -Real.log (500000000000 / 582357678083) ≤ (19059591 / 125000000) := by
  have h := checkLog_sound (w := (82357678083 / 1082357678083)) (n := 12)
    (lo := (152476727 / 1000000000)) (hi := (19059591 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582357678083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582357678083 / 500000000000) = 1/(500000000000 / 582357678083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_231 : Bounds (152476727 / 1000000000) (19059591 / 125000000) (Real.log (582357678083 / 500000000000)) := by
  have h := reflection_log_231_neg
  have he : Real.log (582357678083 / 500000000000) = -Real.log (500000000000 / 582357678083) := by
    rw [show ((582357678083 / 500000000000) : ℝ) = ((500000000000 / 582357678083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_232_neg : (76442549 / 500000000) ≤ -Real.log (50000000000 / 58259554447) ∧
    -Real.log (50000000000 / 58259554447) ≤ (152885099 / 1000000000) := by
  have h := checkLog_sound (w := (8259554447 / 108259554447)) (n := 12)
    (lo := (76442549 / 500000000)) (hi := (152885099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58259554447 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58259554447 / 50000000000) = 1/(50000000000 / 58259554447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_232 : Bounds (76442549 / 500000000) (152885099 / 1000000000) (Real.log (58259554447 / 50000000000)) := by
  have h := reflection_log_232_neg
  have he : Real.log (58259554447 / 50000000000) = -Real.log (50000000000 / 58259554447) := by
    rw [show ((58259554447 / 50000000000) : ℝ) = ((50000000000 / 58259554447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_233_neg : (305760043 / 1000000000) ≤ -Real.log (125000000000 / 169707061181) ∧
    -Real.log (125000000000 / 169707061181) ≤ (76440011 / 250000000) := by
  have h := checkLog_sound (w := (44707061181 / 294707061181)) (n := 12)
    (lo := (305760043 / 1000000000)) (hi := (76440011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169707061181 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169707061181 / 125000000000) = 1/(125000000000 / 169707061181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_233 : Bounds (305760043 / 1000000000) (76440011 / 250000000) (Real.log (169707061181 / 125000000000)) := by
  have h := reflection_log_233_neg
  have he : Real.log (169707061181 / 125000000000) = -Real.log (125000000000 / 169707061181) := by
    rw [show ((169707061181 / 125000000000) : ℝ) = ((125000000000 / 169707061181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_234_neg : (152982379 / 500000000) ≤ -Real.log (62500000000 / 84870903089) ∧
    -Real.log (62500000000 / 84870903089) ≤ (305964759 / 1000000000) := by
  have h := checkLog_sound (w := (22370903089 / 147370903089)) (n := 12)
    (lo := (152982379 / 500000000)) (hi := (305964759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84870903089 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84870903089 / 62500000000) = 1/(62500000000 / 84870903089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_234 : Bounds (152982379 / 500000000) (305964759 / 1000000000) (Real.log (84870903089 / 62500000000)) := by
  have h := reflection_log_234_neg
  have he : Real.log (84870903089 / 62500000000) = -Real.log (62500000000 / 84870903089) := by
    rw [show ((84870903089 / 62500000000) : ℝ) = ((62500000000 / 84870903089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_235_neg : (8838297 / 62500000) ≤ -Real.log (10000 / 11519) ∧
    -Real.log (10000 / 11519) ≤ (141412753 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 21519)) (n := 12)
    (lo := (8838297 / 62500000)) (hi := (141412753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11519 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11519 / 10000) = 1/(10000 / 11519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_235 : Bounds (8838297 / 62500000) (141412753 / 1000000000) (Real.log (11519 / 10000)) := by
  have h := reflection_log_235_neg
  have he : Real.log (11519 / 10000) = -Real.log (10000 / 11519) := by
    rw [show ((11519 / 10000) : ℝ) = ((10000 / 11519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_236_neg : (6590269 / 40000000) ≤ -Real.log (8481 / 10000) ∧
    -Real.log (8481 / 10000) ≤ (82378363 / 500000000) := by
  have h := checkLog_sound (w := (1519 / 18481)) (n := 12)
    (lo := (6590269 / 40000000)) (hi := (82378363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8481) = 1/(8481 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_236 : Bounds (-82378363 / 500000000) (-6590269 / 40000000) (Real.log (8481 / 10000)) := by
  have h := reflection_log_236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_237_neg : (9493 / 62500000) ≤ -Real.log (10000000 / 10001519) ∧
    -Real.log (10000000 / 10001519) ≤ (151889 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 20001519)) (n := 12)
    (lo := (9493 / 62500000)) (hi := (151889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001519 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001519 / 10000000) = 1/(10000000 / 10001519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_237 : Bounds (9493 / 62500000) (151889 / 1000000000) (Real.log (10001519 / 10000000)) := by
  have h := reflection_log_237_neg
  have he : Real.log (10001519 / 10000000) = -Real.log (10000000 / 10001519) := by
    rw [show ((10001519 / 10000000) : ℝ) = ((10000000 / 10001519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_238_neg : (151911 / 1000000000) ≤ -Real.log (9998481 / 10000000) ∧
    -Real.log (9998481 / 10000000) ≤ (18989 / 125000000) := by
  have h := checkLog_sound (w := (1519 / 19998481)) (n := 12)
    (lo := (151911 / 1000000000)) (hi := (18989 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998481) = 1/(9998481 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_238 : Bounds (-18989 / 125000000) (-151911 / 1000000000) (Real.log (9998481 / 10000000)) := by
  have h := reflection_log_238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_239_neg : (36690747 / 500000000) ≤ -Real.log (1000000 / 1076141) ∧
    -Real.log (1000000 / 1076141) ≤ (14676299 / 200000000) := by
  have h := checkLog_sound (w := (76141 / 2076141)) (n := 12)
    (lo := (36690747 / 500000000)) (hi := (14676299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076141 / 1000000) = 1/(1000000 / 1076141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_239 : Bounds (36690747 / 500000000) (14676299 / 200000000) (Real.log (1076141 / 1000000)) := by
  have h := reflection_log_239_neg
  have he : Real.log (1076141 / 1000000) = -Real.log (1000000 / 1076141) := by
    rw [show ((1076141 / 1000000) : ℝ) = ((1000000 / 1076141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_240_neg : (9899477 / 125000000) ≤ -Real.log (923859 / 1000000) ∧
    -Real.log (923859 / 1000000) ≤ (79195817 / 1000000000) := by
  have h := checkLog_sound (w := (76141 / 1923859)) (n := 12)
    (lo := (9899477 / 125000000)) (hi := (79195817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923859) = 1/(923859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_240 : Bounds (-79195817 / 1000000000) (-9899477 / 125000000) (Real.log (923859 / 1000000)) := by
  have h := reflection_log_240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_241_neg : (73570113 / 1000000000) ≤ -Real.log (125000 / 134543) ∧
    -Real.log (125000 / 134543) ≤ (36785057 / 500000000) := by
  have h := checkLog_sound (w := (9543 / 259543)) (n := 12)
    (lo := (73570113 / 1000000000)) (hi := (36785057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134543 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134543 / 125000) = 1/(125000 / 134543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_241 : Bounds (73570113 / 1000000000) (36785057 / 500000000) (Real.log (134543 / 125000)) := by
  have h := reflection_log_241_neg
  have he : Real.log (134543 / 125000) = -Real.log (125000 / 134543) := by
    rw [show ((134543 / 125000) : ℝ) = ((125000 / 134543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_242_neg : (79415571 / 1000000000) ≤ -Real.log (115457 / 125000) ∧
    -Real.log (115457 / 125000) ≤ (19853893 / 250000000) := by
  have h := checkLog_sound (w := (9543 / 240457)) (n := 12)
    (lo := (79415571 / 1000000000)) (hi := (19853893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115457) = 1/(115457 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_242 : Bounds (-19853893 / 250000000) (-79415571 / 1000000000) (Real.log (115457 / 125000)) := by
  have h := reflection_log_242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_243_neg : (5845457 / 1000000000) ≤ -Real.log (15533931151 / 15625000000) ∧
    -Real.log (15533931151 / 15625000000) ≤ (2922729 / 500000000) := by
  have h := checkLog_sound (w := (91068849 / 31158931151)) (n := 12)
    (lo := (5845457 / 1000000000)) (hi := (2922729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15533931151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15533931151) = 1/(15533931151 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_243 : Bounds (-2922729 / 500000000) (-5845457 / 1000000000) (Real.log (15533931151 / 15625000000)) := by
  have h := reflection_log_243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_244_neg : (2907161 / 500000000) ≤ -Real.log (994202548119 / 1000000000000) ∧
    -Real.log (994202548119 / 1000000000000) ≤ (5814323 / 1000000000) := by
  have h := checkLog_sound (w := (5797451881 / 1994202548119)) (n := 12)
    (lo := (2907161 / 500000000)) (hi := (5814323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994202548119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994202548119) = 1/(994202548119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_244 : Bounds (-5814323 / 1000000000) (-2907161 / 500000000) (Real.log (994202548119 / 1000000000000)) := by
  have h := reflection_log_244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_245_neg : (15257731 / 100000000) ≤ -Real.log (3125000000 / 3640101601) ∧
    -Real.log (3125000000 / 3640101601) ≤ (152577311 / 1000000000) := by
  have h := checkLog_sound (w := (515101601 / 6765101601)) (n := 12)
    (lo := (15257731 / 100000000)) (hi := (152577311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3640101601 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3640101601 / 3125000000) = 1/(3125000000 / 3640101601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_245 : Bounds (15257731 / 100000000) (152577311 / 1000000000) (Real.log (3640101601 / 3125000000)) := by
  have h := reflection_log_245_neg
  have he : Real.log (3640101601 / 3125000000) = -Real.log (3125000000 / 3640101601) := by
    rw [show ((3640101601 / 3125000000) : ℝ) = ((3125000000 / 3640101601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_246_neg : (38246421 / 250000000) ≤ -Real.log (250000000000 / 291327074149) ∧
    -Real.log (250000000000 / 291327074149) ≤ (30597137 / 200000000) := by
  have h := checkLog_sound (w := (41327074149 / 541327074149)) (n := 12)
    (lo := (38246421 / 250000000)) (hi := (30597137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291327074149 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291327074149 / 250000000000) = 1/(250000000000 / 291327074149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_246 : Bounds (38246421 / 250000000) (30597137 / 200000000) (Real.log (291327074149 / 250000000000)) := by
  have h := reflection_log_246_neg
  have he : Real.log (291327074149 / 250000000000) = -Real.log (250000000000 / 291327074149) := by
    rw [show ((291327074149 / 250000000000) : ℝ) = ((250000000000 / 291327074149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_247_neg : (152982379 / 500000000) ≤ -Real.log (500000000000 / 678967224711) ∧
    -Real.log (500000000000 / 678967224711) ≤ (305964759 / 1000000000) := by
  have h := checkLog_sound (w := (178967224711 / 1178967224711)) (n := 12)
    (lo := (152982379 / 500000000)) (hi := (305964759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678967224711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678967224711 / 500000000000) = 1/(500000000000 / 678967224711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_247 : Bounds (152982379 / 500000000) (305964759 / 1000000000) (Real.log (678967224711 / 500000000000)) := by
  have h := reflection_log_247_neg
  have he : Real.log (678967224711 / 500000000000) = -Real.log (500000000000 / 678967224711) := by
    rw [show ((678967224711 / 500000000000) : ℝ) = ((500000000000 / 678967224711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_248_neg : (153084739 / 500000000) ≤ -Real.log (15625000000 / 21222069921) ∧
    -Real.log (15625000000 / 21222069921) ≤ (306169479 / 1000000000) := by
  have h := checkLog_sound (w := (5597069921 / 36847069921)) (n := 12)
    (lo := (153084739 / 500000000)) (hi := (306169479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21222069921 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21222069921 / 15625000000) = 1/(15625000000 / 21222069921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_248 : Bounds (153084739 / 500000000) (306169479 / 1000000000) (Real.log (21222069921 / 15625000000)) := by
  have h := reflection_log_248_neg
  have he : Real.log (21222069921 / 15625000000) = -Real.log (15625000000 / 21222069921) := by
    rw [show ((21222069921 / 15625000000) : ℝ) = ((15625000000 / 21222069921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_249_neg : (70749781 / 500000000) ≤ -Real.log (125 / 144) ∧
    -Real.log (125 / 144) ≤ (141499563 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 269)) (n := 12)
    (lo := (70749781 / 500000000)) (hi := (141499563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144 / 125) = 1/(125 / 144) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_249 : Bounds (70749781 / 500000000) (141499563 / 1000000000) (Real.log (144 / 125)) := by
  have h := reflection_log_249_neg
  have he : Real.log (144 / 125) = -Real.log (125 / 144) := by
    rw [show ((144 / 125) : ℝ) = ((125 / 144) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_250_neg : (164874643 / 1000000000) ≤ -Real.log (106 / 125) ∧
    -Real.log (106 / 125) ≤ (41218661 / 250000000) := by
  have h := checkLog_sound (w := (19 / 231)) (n := 12)
    (lo := (164874643 / 1000000000)) (hi := (41218661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 106) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 106) = 1/(106 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_250 : Bounds (-41218661 / 250000000) (-164874643 / 1000000000) (Real.log (106 / 125)) := by
  have h := reflection_log_250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_251_neg : (37997 / 250000000) ≤ -Real.log (125000 / 125019) ∧
    -Real.log (125000 / 125019) ≤ (151989 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 250019)) (n := 12)
    (lo := (37997 / 250000000)) (hi := (151989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125019 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125019 / 125000) = 1/(125000 / 125019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_251 : Bounds (37997 / 250000000) (151989 / 1000000000) (Real.log (125019 / 125000)) := by
  have h := reflection_log_251_neg
  have he : Real.log (125019 / 125000) = -Real.log (125000 / 125019) := by
    rw [show ((125019 / 125000) : ℝ) = ((125000 / 125019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_252_neg : (152011 / 1000000000) ≤ -Real.log (124981 / 125000) ∧
    -Real.log (124981 / 125000) ≤ (38003 / 250000000) := by
  have h := checkLog_sound (w := (19 / 249981)) (n := 12)
    (lo := (152011 / 1000000000)) (hi := (38003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124981) = 1/(124981 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_252 : Bounds (-38003 / 250000000) (-152011 / 1000000000) (Real.log (124981 / 125000)) := by
  have h := reflection_log_252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_253_neg : (36808747 / 500000000) ≤ -Real.log (200000 / 215279) ∧
    -Real.log (200000 / 215279) ≤ (14723499 / 200000000) := by
  have h := checkLog_sound (w := (15279 / 415279)) (n := 12)
    (lo := (36808747 / 500000000)) (hi := (14723499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215279 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215279 / 200000) = 1/(200000 / 215279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_253 : Bounds (36808747 / 500000000) (14723499 / 200000000) (Real.log (215279 / 200000)) := by
  have h := reflection_log_253_neg
  have he : Real.log (215279 / 200000) = -Real.log (200000 / 215279) := by
    rw [show ((215279 / 200000) : ℝ) = ((200000 / 215279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_254_neg : (79470787 / 1000000000) ≤ -Real.log (184721 / 200000) ∧
    -Real.log (184721 / 200000) ≤ (19867697 / 250000000) := by
  have h := checkLog_sound (w := (15279 / 384721)) (n := 12)
    (lo := (79470787 / 1000000000)) (hi := (19867697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184721) = 1/(184721 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_254 : Bounds (-19867697 / 250000000) (-79470787 / 1000000000) (Real.log (184721 / 200000)) := by
  have h := reflection_log_254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_255_neg : (5853293 / 1000000000) ≤ -Real.log (39766552159 / 40000000000) ∧
    -Real.log (39766552159 / 40000000000) ≤ (2926647 / 500000000) := by
  have h := checkLog_sound (w := (233447841 / 79766552159)) (n := 12)
    (lo := (5853293 / 1000000000)) (hi := (2926647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39766552159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39766552159) = 1/(39766552159 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_255 : Bounds (-2926647 / 500000000) (-5853293 / 1000000000) (Real.log (39766552159 / 40000000000)) := by
  have h := reflection_log_255_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0004 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_256_neg : (30535981 / 200000000) ≤ -Real.log (500000000000 / 582476012331) ∧
    -Real.log (500000000000 / 582476012331) ≤ (76339953 / 500000000) := by
  have h := checkLog_sound (w := (82476012331 / 1082476012331)) (n := 12)
    (lo := (30535981 / 200000000)) (hi := (76339953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582476012331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582476012331 / 500000000000) = 1/(500000000000 / 582476012331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_256 : Bounds (30535981 / 200000000) (76339953 / 500000000) (Real.log (582476012331 / 500000000000)) := by
  have h := reflection_log_256_neg
  have he : Real.log (582476012331 / 500000000000) = -Real.log (500000000000 / 582476012331) := by
    rw [show ((582476012331 / 500000000000) : ℝ) = ((500000000000 / 582476012331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_257_neg : (76544141 / 500000000) ≤ -Real.log (500000000000 / 582713930739) ∧
    -Real.log (500000000000 / 582713930739) ≤ (153088283 / 1000000000) := by
  have h := checkLog_sound (w := (82713930739 / 1082713930739)) (n := 12)
    (lo := (76544141 / 500000000)) (hi := (153088283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582713930739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582713930739 / 500000000000) = 1/(500000000000 / 582713930739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_257 : Bounds (76544141 / 500000000) (153088283 / 1000000000) (Real.log (582713930739 / 500000000000)) := by
  have h := reflection_log_257_neg
  have he : Real.log (582713930739 / 500000000000) = -Real.log (500000000000 / 582713930739) := by
    rw [show ((582713930739 / 500000000000) : ℝ) = ((500000000000 / 582713930739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_258_neg : (153084739 / 500000000) ≤ -Real.log (500000000000 / 679106237471) ∧
    -Real.log (500000000000 / 679106237471) ≤ (306169479 / 1000000000) := by
  have h := checkLog_sound (w := (179106237471 / 1179106237471)) (n := 12)
    (lo := (153084739 / 500000000)) (hi := (306169479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679106237471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679106237471 / 500000000000) = 1/(500000000000 / 679106237471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_258 : Bounds (153084739 / 500000000) (306169479 / 1000000000) (Real.log (679106237471 / 500000000000)) := by
  have h := reflection_log_258_neg
  have he : Real.log (679106237471 / 500000000000) = -Real.log (500000000000 / 679106237471) := by
    rw [show ((679106237471 / 500000000000) : ℝ) = ((500000000000 / 679106237471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_259_neg : (61274841 / 200000000) ≤ -Real.log (500000000000 / 679245283019) ∧
    -Real.log (500000000000 / 679245283019) ≤ (153187103 / 500000000) := by
  have h := checkLog_sound (w := (179245283019 / 1179245283019)) (n := 12)
    (lo := (61274841 / 200000000)) (hi := (153187103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679245283019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679245283019 / 500000000000) = 1/(500000000000 / 679245283019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_259 : Bounds (61274841 / 200000000) (153187103 / 500000000) (Real.log (679245283019 / 500000000000)) := by
  have h := reflection_log_259_neg
  have he : Real.log (679245283019 / 500000000000) = -Real.log (500000000000 / 679245283019) := by
    rw [show ((679245283019 / 500000000000) : ℝ) = ((500000000000 / 679245283019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_260_neg : (35396591 / 250000000) ≤ -Real.log (10000 / 11521) ∧
    -Real.log (10000 / 11521) ≤ (28317273 / 200000000) := by
  have h := checkLog_sound (w := (1521 / 21521)) (n := 12)
    (lo := (35396591 / 250000000)) (hi := (28317273 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11521 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11521 / 10000) = 1/(10000 / 11521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_260 : Bounds (35396591 / 250000000) (28317273 / 200000000) (Real.log (11521 / 10000)) := by
  have h := reflection_log_260_neg
  have he : Real.log (11521 / 10000) = -Real.log (10000 / 11521) := by
    rw [show ((11521 / 10000) : ℝ) = ((10000 / 11521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_261_neg : (82496287 / 500000000) ≤ -Real.log (8479 / 10000) ∧
    -Real.log (8479 / 10000) ≤ (6599703 / 40000000) := by
  have h := checkLog_sound (w := (1521 / 18479)) (n := 12)
    (lo := (82496287 / 500000000)) (hi := (6599703 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8479) = 1/(8479 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_261 : Bounds (-6599703 / 40000000) (-82496287 / 500000000) (Real.log (8479 / 10000)) := by
  have h := reflection_log_261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_262_neg : (19011 / 125000000) ≤ -Real.log (10000000 / 10001521) ∧
    -Real.log (10000000 / 10001521) ≤ (152089 / 1000000000) := by
  have h := checkLog_sound (w := (1521 / 20001521)) (n := 12)
    (lo := (19011 / 125000000)) (hi := (152089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001521 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001521 / 10000000) = 1/(10000000 / 10001521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_262 : Bounds (19011 / 125000000) (152089 / 1000000000) (Real.log (10001521 / 10000000)) := by
  have h := reflection_log_262_neg
  have he : Real.log (10001521 / 10000000) = -Real.log (10000000 / 10001521) := by
    rw [show ((10001521 / 10000000) : ℝ) = ((10000000 / 10001521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_263_neg : (152111 / 1000000000) ≤ -Real.log (9998479 / 10000000) ∧
    -Real.log (9998479 / 10000000) ≤ (9507 / 62500000) := by
  have h := checkLog_sound (w := (1521 / 19998479)) (n := 12)
    (lo := (152111 / 1000000000)) (hi := (9507 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998479) = 1/(9998479 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_263 : Bounds (-9507 / 62500000) (-152111 / 1000000000) (Real.log (9998479 / 10000000)) := by
  have h := reflection_log_263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_264_neg : (36832437 / 500000000) ≤ -Real.log (500000 / 538223) ∧
    -Real.log (500000 / 538223) ≤ (589319 / 8000000) := by
  have h := checkLog_sound (w := (38223 / 1038223)) (n := 12)
    (lo := (36832437 / 500000000)) (hi := (589319 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538223 / 500000) = 1/(500000 / 538223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_264 : Bounds (36832437 / 500000000) (589319 / 8000000) (Real.log (538223 / 500000)) := by
  have h := reflection_log_264_neg
  have he : Real.log (538223 / 500000) = -Real.log (500000 / 538223) := by
    rw [show ((538223 / 500000) : ℝ) = ((500000 / 538223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_265_neg : (79526007 / 1000000000) ≤ -Real.log (461777 / 500000) ∧
    -Real.log (461777 / 500000) ≤ (9940751 / 125000000) := by
  have h := checkLog_sound (w := (38223 / 961777)) (n := 12)
    (lo := (79526007 / 1000000000)) (hi := (9940751 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461777) = 1/(461777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_265 : Bounds (-9940751 / 125000000) (-79526007 / 1000000000) (Real.log (461777 / 500000)) := by
  have h := reflection_log_265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_266_neg : (5861133 / 1000000000) ≤ -Real.log (248539002271 / 250000000000) ∧
    -Real.log (248539002271 / 250000000000) ≤ (2930567 / 500000000) := by
  have h := checkLog_sound (w := (1460997729 / 498539002271)) (n := 12)
    (lo := (5861133 / 1000000000)) (hi := (2930567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248539002271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248539002271) = 1/(248539002271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_266 : Bounds (-2930567 / 500000000) (-5861133 / 1000000000) (Real.log (248539002271 / 250000000000)) := by
  have h := reflection_log_266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_267_neg : (152782501 / 1000000000) ≤ -Real.log (500000000000 / 582535775101) ∧
    -Real.log (500000000000 / 582535775101) ≤ (76391251 / 500000000) := by
  have h := checkLog_sound (w := (82535775101 / 1082535775101)) (n := 12)
    (lo := (152782501 / 1000000000)) (hi := (76391251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582535775101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582535775101 / 500000000000) = 1/(500000000000 / 582535775101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_267 : Bounds (152782501 / 1000000000) (76391251 / 500000000) (Real.log (582535775101 / 500000000000)) := by
  have h := reflection_log_267_neg
  have he : Real.log (582535775101 / 500000000000) = -Real.log (500000000000 / 582535775101) := by
    rw [show ((582535775101 / 500000000000) : ℝ) = ((500000000000 / 582535775101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_268_neg : (153190881 / 1000000000) ≤ -Real.log (500000000000 / 582773719783) ∧
    -Real.log (500000000000 / 582773719783) ≤ (76595441 / 500000000) := by
  have h := checkLog_sound (w := (82773719783 / 1082773719783)) (n := 12)
    (lo := (153190881 / 1000000000)) (hi := (76595441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582773719783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582773719783 / 500000000000) = 1/(500000000000 / 582773719783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_268 : Bounds (153190881 / 1000000000) (76595441 / 500000000) (Real.log (582773719783 / 500000000000)) := by
  have h := reflection_log_268_neg
  have he : Real.log (582773719783 / 500000000000) = -Real.log (500000000000 / 582773719783) := by
    rw [show ((582773719783 / 500000000000) : ℝ) = ((500000000000 / 582773719783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_269_neg : (61274841 / 200000000) ≤ -Real.log (250000000000 / 339622641509) ∧
    -Real.log (250000000000 / 339622641509) ≤ (153187103 / 500000000) := by
  have h := checkLog_sound (w := (89622641509 / 589622641509)) (n := 12)
    (lo := (61274841 / 200000000)) (hi := (153187103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339622641509 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339622641509 / 250000000000) = 1/(250000000000 / 339622641509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_269 : Bounds (61274841 / 200000000) (153187103 / 500000000) (Real.log (339622641509 / 250000000000)) := by
  have h := reflection_log_269_neg
  have he : Real.log (339622641509 / 250000000000) = -Real.log (250000000000 / 339622641509) := by
    rw [show ((339622641509 / 250000000000) : ℝ) = ((250000000000 / 339622641509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_270_neg : (153289469 / 500000000) ≤ -Real.log (125000000000 / 169846090341) ∧
    -Real.log (125000000000 / 169846090341) ≤ (306578939 / 1000000000) := by
  have h := checkLog_sound (w := (44846090341 / 294846090341)) (n := 12)
    (lo := (153289469 / 500000000)) (hi := (306578939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169846090341 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169846090341 / 125000000000) = 1/(125000000000 / 169846090341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_270 : Bounds (153289469 / 500000000) (306578939 / 1000000000) (Real.log (169846090341 / 125000000000)) := by
  have h := reflection_log_270_neg
  have he : Real.log (169846090341 / 125000000000) = -Real.log (125000000000 / 169846090341) := by
    rw [show ((169846090341 / 125000000000) : ℝ) = ((125000000000 / 169846090341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_271_neg : (70836579 / 500000000) ≤ -Real.log (5000 / 5761) ∧
    -Real.log (5000 / 5761) ≤ (141673159 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 10761)) (n := 12)
    (lo := (70836579 / 500000000)) (hi := (141673159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5761 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5761 / 5000) = 1/(5000 / 5761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_271 : Bounds (70836579 / 500000000) (141673159 / 1000000000) (Real.log (5761 / 5000)) := by
  have h := reflection_log_271_neg
  have he : Real.log (5761 / 5000) = -Real.log (5000 / 5761) := by
    rw [show ((5761 / 5000) : ℝ) = ((5000 / 5761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_272_neg : (4127763 / 25000000) ≤ -Real.log (4239 / 5000) ∧
    -Real.log (4239 / 5000) ≤ (165110521 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 9239)) (n := 12)
    (lo := (4127763 / 25000000)) (hi := (165110521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4239) = 1/(4239 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_272 : Bounds (-165110521 / 1000000000) (-4127763 / 25000000) (Real.log (4239 / 5000)) := by
  have h := reflection_log_272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_273_neg : (38047 / 250000000) ≤ -Real.log (5000000 / 5000761) ∧
    -Real.log (5000000 / 5000761) ≤ (152189 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 10000761)) (n := 12)
    (lo := (38047 / 250000000)) (hi := (152189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000761 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000761 / 5000000) = 1/(5000000 / 5000761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_273 : Bounds (38047 / 250000000) (152189 / 1000000000) (Real.log (5000761 / 5000000)) := by
  have h := reflection_log_273_neg
  have he : Real.log (5000761 / 5000000) = -Real.log (5000000 / 5000761) := by
    rw [show ((5000761 / 5000000) : ℝ) = ((5000000 / 5000761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_274_neg : (152211 / 1000000000) ≤ -Real.log (4999239 / 5000000) ∧
    -Real.log (4999239 / 5000000) ≤ (38053 / 250000000) := by
  have h := checkLog_sound (w := (761 / 9999239)) (n := 12)
    (lo := (152211 / 1000000000)) (hi := (38053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999239) = 1/(4999239 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_274 : Bounds (-38053 / 250000000) (-152211 / 1000000000) (Real.log (4999239 / 5000000)) := by
  have h := reflection_log_274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_275_neg : (73522729 / 1000000000) ≤ -Real.log (1000000 / 1076293) ∧
    -Real.log (1000000 / 1076293) ≤ (7352273 / 100000000) := by
  have h := checkLog_sound (w := (76293 / 2076293)) (n := 12)
    (lo := (73522729 / 1000000000)) (hi := (7352273 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076293 / 1000000) = 1/(1000000 / 1076293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_275 : Bounds (73522729 / 1000000000) (7352273 / 100000000) (Real.log (1076293 / 1000000)) := by
  have h := reflection_log_275_neg
  have he : Real.log (1076293 / 1000000) = -Real.log (1000000 / 1076293) := by
    rw [show ((1076293 / 1000000) : ℝ) = ((1000000 / 1076293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_276_neg : (79360357 / 1000000000) ≤ -Real.log (923707 / 1000000) ∧
    -Real.log (923707 / 1000000) ≤ (39680179 / 500000000) := by
  have h := checkLog_sound (w := (76293 / 1923707)) (n := 12)
    (lo := (79360357 / 1000000000)) (hi := (39680179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923707) = 1/(923707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_276 : Bounds (-39680179 / 500000000) (-79360357 / 1000000000) (Real.log (923707 / 1000000)) := by
  have h := reflection_log_276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_277_neg : (36855661 / 500000000) ≤ -Real.log (62500 / 67281) ∧
    -Real.log (62500 / 67281) ≤ (73711323 / 1000000000) := by
  have h := checkLog_sound (w := (4781 / 129781)) (n := 12)
    (lo := (36855661 / 500000000)) (hi := (73711323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67281 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67281 / 62500) = 1/(62500 / 67281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_277 : Bounds (36855661 / 500000000) (73711323 / 1000000000) (Real.log (67281 / 62500)) := by
  have h := reflection_log_277_neg
  have he : Real.log (67281 / 62500) = -Real.log (62500 / 67281) := by
    rw [show ((67281 / 62500) : ℝ) = ((62500 / 67281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_278_neg : (19895037 / 250000000) ≤ -Real.log (57719 / 62500) ∧
    -Real.log (57719 / 62500) ≤ (79580149 / 1000000000) := by
  have h := checkLog_sound (w := (4781 / 120219)) (n := 12)
    (lo := (19895037 / 250000000)) (hi := (79580149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57719) = 1/(57719 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_278 : Bounds (-79580149 / 1000000000) (-19895037 / 250000000) (Real.log (57719 / 62500)) := by
  have h := reflection_log_278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_279_neg : (234753 / 40000000) ≤ -Real.log (3883392039 / 3906250000) ∧
    -Real.log (3883392039 / 3906250000) ≤ (2934413 / 500000000) := by
  have h := checkLog_sound (w := (22857961 / 7789642039)) (n := 12)
    (lo := (234753 / 40000000)) (hi := (2934413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3883392039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3883392039) = 1/(3883392039 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_279 : Bounds (-2934413 / 500000000) (-234753 / 40000000) (Real.log (3883392039 / 3906250000)) := by
  have h := reflection_log_279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_280_neg : (5837627 / 1000000000) ≤ -Real.log (994179378151 / 1000000000000) ∧
    -Real.log (994179378151 / 1000000000000) ≤ (1459407 / 250000000) := by
  have h := checkLog_sound (w := (5820621849 / 1994179378151)) (n := 12)
    (lo := (5837627 / 1000000000)) (hi := (1459407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994179378151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994179378151) = 1/(994179378151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_280 : Bounds (-1459407 / 250000000) (-5837627 / 1000000000) (Real.log (994179378151 / 1000000000000)) := by
  have h := reflection_log_280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_281_neg : (76441543 / 500000000) ≤ -Real.log (500000000000 / 582594372457) ∧
    -Real.log (500000000000 / 582594372457) ≤ (152883087 / 1000000000) := by
  have h := checkLog_sound (w := (82594372457 / 1082594372457)) (n := 12)
    (lo := (76441543 / 500000000)) (hi := (152883087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582594372457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582594372457 / 500000000000) = 1/(500000000000 / 582594372457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_281 : Bounds (76441543 / 500000000) (152883087 / 1000000000) (Real.log (582594372457 / 500000000000)) := by
  have h := reflection_log_281_neg
  have he : Real.log (582594372457 / 500000000000) = -Real.log (500000000000 / 582594372457) := by
    rw [show ((582594372457 / 500000000000) : ℝ) = ((500000000000 / 582594372457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_282_neg : (15329147 / 100000000) ≤ -Real.log (500000000000 / 582832342903) ∧
    -Real.log (500000000000 / 582832342903) ≤ (153291471 / 1000000000) := by
  have h := checkLog_sound (w := (82832342903 / 1082832342903)) (n := 12)
    (lo := (15329147 / 100000000)) (hi := (153291471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582832342903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582832342903 / 500000000000) = 1/(500000000000 / 582832342903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_282 : Bounds (15329147 / 100000000) (153291471 / 1000000000) (Real.log (582832342903 / 500000000000)) := by
  have h := reflection_log_282_neg
  have he : Real.log (582832342903 / 500000000000) = -Real.log (500000000000 / 582832342903) := by
    rw [show ((582832342903 / 500000000000) : ℝ) = ((500000000000 / 582832342903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_283_neg : (153289469 / 500000000) ≤ -Real.log (500000000000 / 679384361363) ∧
    -Real.log (500000000000 / 679384361363) ≤ (306578939 / 1000000000) := by
  have h := checkLog_sound (w := (179384361363 / 1179384361363)) (n := 12)
    (lo := (153289469 / 500000000)) (hi := (306578939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679384361363 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679384361363 / 500000000000) = 1/(500000000000 / 679384361363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_283 : Bounds (153289469 / 500000000) (306578939 / 1000000000) (Real.log (679384361363 / 500000000000)) := by
  have h := reflection_log_283_neg
  have he : Real.log (679384361363 / 500000000000) = -Real.log (500000000000 / 679384361363) := by
    rw [show ((679384361363 / 500000000000) : ℝ) = ((500000000000 / 679384361363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_284_neg : (153391839 / 500000000) ≤ -Real.log (250000000000 / 339761736259) ∧
    -Real.log (250000000000 / 339761736259) ≤ (306783679 / 1000000000) := by
  have h := checkLog_sound (w := (89761736259 / 589761736259)) (n := 12)
    (lo := (153391839 / 500000000)) (hi := (306783679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339761736259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339761736259 / 250000000000) = 1/(250000000000 / 339761736259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_284 : Bounds (153391839 / 500000000) (306783679 / 1000000000) (Real.log (339761736259 / 250000000000)) := by
  have h := reflection_log_284_neg
  have he : Real.log (339761736259 / 250000000000) = -Real.log (250000000000 / 339761736259) := by
    rw [show ((339761736259 / 250000000000) : ℝ) = ((250000000000 / 339761736259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_285_neg : (28351989 / 200000000) ≤ -Real.log (10000 / 11523) ∧
    -Real.log (10000 / 11523) ≤ (70879973 / 500000000) := by
  have h := checkLog_sound (w := (1523 / 21523)) (n := 12)
    (lo := (28351989 / 200000000)) (hi := (70879973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11523 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11523 / 10000) = 1/(10000 / 11523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_285 : Bounds (28351989 / 200000000) (70879973 / 500000000) (Real.log (11523 / 10000)) := by
  have h := reflection_log_285_neg
  have he : Real.log (11523 / 10000) = -Real.log (10000 / 11523) := by
    rw [show ((11523 / 10000) : ℝ) = ((10000 / 11523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_286_neg : (165228479 / 1000000000) ≤ -Real.log (8477 / 10000) ∧
    -Real.log (8477 / 10000) ≤ (516339 / 3125000) := by
  have h := checkLog_sound (w := (1523 / 18477)) (n := 12)
    (lo := (165228479 / 1000000000)) (hi := (516339 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8477) = 1/(8477 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_286 : Bounds (-516339 / 3125000) (-165228479 / 1000000000) (Real.log (8477 / 10000)) := by
  have h := reflection_log_286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_287_neg : (4759 / 31250000) ≤ -Real.log (10000000 / 10001523) ∧
    -Real.log (10000000 / 10001523) ≤ (152289 / 1000000000) := by
  have h := checkLog_sound (w := (1523 / 20001523)) (n := 12)
    (lo := (4759 / 31250000)) (hi := (152289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001523 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001523 / 10000000) = 1/(10000000 / 10001523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_287 : Bounds (4759 / 31250000) (152289 / 1000000000) (Real.log (10001523 / 10000000)) := by
  have h := reflection_log_287_neg
  have he : Real.log (10001523 / 10000000) = -Real.log (10000000 / 10001523) := by
    rw [show ((10001523 / 10000000) : ℝ) = ((10000000 / 10001523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_288_neg : (152311 / 1000000000) ≤ -Real.log (9998477 / 10000000) ∧
    -Real.log (9998477 / 10000000) ≤ (19039 / 125000000) := by
  have h := checkLog_sound (w := (1523 / 19998477)) (n := 12)
    (lo := (152311 / 1000000000)) (hi := (19039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998477) = 1/(9998477 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_288 : Bounds (-19039 / 125000000) (-152311 / 1000000000) (Real.log (9998477 / 10000000)) := by
  have h := reflection_log_288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_289_neg : (9219837 / 125000000) ≤ -Real.log (1000000 / 1076547) ∧
    -Real.log (1000000 / 1076547) ≤ (73758697 / 1000000000) := by
  have h := checkLog_sound (w := (76547 / 2076547)) (n := 12)
    (lo := (9219837 / 125000000)) (hi := (73758697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076547 / 1000000) = 1/(1000000 / 1076547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_289 : Bounds (9219837 / 125000000) (73758697 / 1000000000) (Real.log (1076547 / 1000000)) := by
  have h := reflection_log_289_neg
  have he : Real.log (1076547 / 1000000) = -Real.log (1000000 / 1076547) := by
    rw [show ((1076547 / 1000000) : ℝ) = ((1000000 / 1076547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_290_neg : (79635373 / 1000000000) ≤ -Real.log (923453 / 1000000) ∧
    -Real.log (923453 / 1000000) ≤ (39817687 / 500000000) := by
  have h := checkLog_sound (w := (76547 / 1923453)) (n := 12)
    (lo := (79635373 / 1000000000)) (hi := (39817687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923453) = 1/(923453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_290 : Bounds (-39817687 / 500000000) (-79635373 / 1000000000) (Real.log (923453 / 1000000)) := by
  have h := reflection_log_290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_291_neg : (5876677 / 1000000000) ≤ -Real.log (994140556791 / 1000000000000) ∧
    -Real.log (994140556791 / 1000000000000) ≤ (2938339 / 500000000) := by
  have h := checkLog_sound (w := (5859443209 / 1994140556791)) (n := 12)
    (lo := (5876677 / 1000000000)) (hi := (2938339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994140556791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994140556791) = 1/(994140556791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_291 : Bounds (-2938339 / 500000000) (-5876677 / 1000000000) (Real.log (994140556791 / 1000000000000)) := by
  have h := reflection_log_291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_292_neg : (38246421 / 250000000) ≤ -Real.log (500000000000 / 582654148297) ∧
    -Real.log (500000000000 / 582654148297) ≤ (30597137 / 200000000) := by
  have h := checkLog_sound (w := (82654148297 / 1082654148297)) (n := 12)
    (lo := (38246421 / 250000000)) (hi := (30597137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582654148297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582654148297 / 500000000000) = 1/(500000000000 / 582654148297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_292 : Bounds (38246421 / 250000000) (30597137 / 200000000) (Real.log (582654148297 / 500000000000)) := by
  have h := reflection_log_292_neg
  have he : Real.log (582654148297 / 500000000000) = -Real.log (500000000000 / 582654148297) := by
    rw [show ((582654148297 / 500000000000) : ℝ) = ((500000000000 / 582654148297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_293_neg : (15339407 / 100000000) ≤ -Real.log (250000000000 / 291446072513) ∧
    -Real.log (250000000000 / 291446072513) ≤ (153394071 / 1000000000) := by
  have h := checkLog_sound (w := (41446072513 / 541446072513)) (n := 12)
    (lo := (15339407 / 100000000)) (hi := (153394071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291446072513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291446072513 / 250000000000) = 1/(250000000000 / 291446072513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_293 : Bounds (15339407 / 100000000) (153394071 / 1000000000) (Real.log (291446072513 / 250000000000)) := by
  have h := reflection_log_293_neg
  have he : Real.log (291446072513 / 250000000000) = -Real.log (250000000000 / 291446072513) := by
    rw [show ((291446072513 / 250000000000) : ℝ) = ((250000000000 / 291446072513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_294_neg : (153391839 / 500000000) ≤ -Real.log (500000000000 / 679523472517) ∧
    -Real.log (500000000000 / 679523472517) ≤ (306783679 / 1000000000) := by
  have h := checkLog_sound (w := (179523472517 / 1179523472517)) (n := 12)
    (lo := (153391839 / 500000000)) (hi := (306783679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679523472517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679523472517 / 500000000000) = 1/(500000000000 / 679523472517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_294 : Bounds (153391839 / 500000000) (306783679 / 1000000000) (Real.log (679523472517 / 500000000000)) := by
  have h := reflection_log_294_neg
  have he : Real.log (679523472517 / 500000000000) = -Real.log (500000000000 / 679523472517) := by
    rw [show ((679523472517 / 500000000000) : ℝ) = ((500000000000 / 679523472517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_295_neg : (38373553 / 125000000) ≤ -Real.log (125000000000 / 169915654123) ∧
    -Real.log (125000000000 / 169915654123) ≤ (12279537 / 40000000) := by
  have h := checkLog_sound (w := (44915654123 / 294915654123)) (n := 12)
    (lo := (38373553 / 125000000)) (hi := (12279537 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169915654123 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169915654123 / 125000000000) = 1/(125000000000 / 169915654123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_295 : Bounds (38373553 / 125000000) (12279537 / 40000000) (Real.log (169915654123 / 125000000000)) := by
  have h := reflection_log_295_neg
  have he : Real.log (169915654123 / 125000000000) = -Real.log (125000000000 / 169915654123) := by
    rw [show ((169915654123 / 125000000000) : ℝ) = ((125000000000 / 169915654123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_296_neg : (35461681 / 250000000) ≤ -Real.log (2500 / 2881) ∧
    -Real.log (2500 / 2881) ≤ (5673869 / 40000000) := by
  have h := checkLog_sound (w := (381 / 5381)) (n := 12)
    (lo := (35461681 / 250000000)) (hi := (5673869 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2881 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2881 / 2500) = 1/(2500 / 2881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_296 : Bounds (35461681 / 250000000) (5673869 / 40000000) (Real.log (2881 / 2500)) := by
  have h := reflection_log_296_neg
  have he : Real.log (2881 / 2500) = -Real.log (2500 / 2881) := by
    rw [show ((2881 / 2500) : ℝ) = ((2500 / 2881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_297_neg : (41336613 / 250000000) ≤ -Real.log (2119 / 2500) ∧
    -Real.log (2119 / 2500) ≤ (165346453 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 4619)) (n := 12)
    (lo := (41336613 / 250000000)) (hi := (165346453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2119) = 1/(2119 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_297 : Bounds (-165346453 / 1000000000) (-41336613 / 250000000) (Real.log (2119 / 2500)) := by
  have h := reflection_log_297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_298_neg : (38097 / 250000000) ≤ -Real.log (2500000 / 2500381) ∧
    -Real.log (2500000 / 2500381) ≤ (152389 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 5000381)) (n := 12)
    (lo := (38097 / 250000000)) (hi := (152389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500381 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500381 / 2500000) = 1/(2500000 / 2500381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_298 : Bounds (38097 / 250000000) (152389 / 1000000000) (Real.log (2500381 / 2500000)) := by
  have h := reflection_log_298_neg
  have he : Real.log (2500381 / 2500000) = -Real.log (2500000 / 2500381) := by
    rw [show ((2500381 / 2500000) : ℝ) = ((2500000 / 2500381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_299_neg : (152411 / 1000000000) ≤ -Real.log (2499619 / 2500000) ∧
    -Real.log (2499619 / 2500000) ≤ (38103 / 250000000) := by
  have h := checkLog_sound (w := (381 / 4999619)) (n := 12)
    (lo := (152411 / 1000000000)) (hi := (38103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499619) = 1/(2499619 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_299 : Bounds (-38103 / 250000000) (-152411 / 1000000000) (Real.log (2499619 / 2500000)) := by
  have h := reflection_log_299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_300_neg : (14723313 / 200000000) ≤ -Real.log (500000 / 538197) ∧
    -Real.log (500000 / 538197) ≤ (36808283 / 500000000) := by
  have h := checkLog_sound (w := (38197 / 1038197)) (n := 12)
    (lo := (14723313 / 200000000)) (hi := (36808283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538197 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538197 / 500000) = 1/(500000 / 538197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_300 : Bounds (14723313 / 200000000) (36808283 / 500000000) (Real.log (538197 / 500000)) := by
  have h := reflection_log_300_neg
  have he : Real.log (538197 / 500000) = -Real.log (500000 / 538197) := by
    rw [show ((538197 / 500000) : ℝ) = ((500000 / 538197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_301_neg : (15893941 / 200000000) ≤ -Real.log (461803 / 500000) ∧
    -Real.log (461803 / 500000) ≤ (39734853 / 500000000) := by
  have h := checkLog_sound (w := (38197 / 961803)) (n := 12)
    (lo := (15893941 / 200000000)) (hi := (39734853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461803) = 1/(461803 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_301 : Bounds (-39734853 / 500000000) (-15893941 / 200000000) (Real.log (461803 / 500000)) := by
  have h := reflection_log_301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_302_neg : (73806069 / 1000000000) ≤ -Real.log (500000 / 538299) ∧
    -Real.log (500000 / 538299) ≤ (7380607 / 100000000) := by
  have h := checkLog_sound (w := (38299 / 1038299)) (n := 12)
    (lo := (73806069 / 1000000000)) (hi := (7380607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538299 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538299 / 500000) = 1/(500000 / 538299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_302 : Bounds (73806069 / 1000000000) (7380607 / 100000000) (Real.log (538299 / 500000)) := by
  have h := reflection_log_302_neg
  have he : Real.log (538299 / 500000) = -Real.log (500000 / 538299) := by
    rw [show ((538299 / 500000) : ℝ) = ((500000 / 538299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_303_neg : (79690603 / 1000000000) ≤ -Real.log (461701 / 500000) ∧
    -Real.log (461701 / 500000) ≤ (19922651 / 250000000) := by
  have h := checkLog_sound (w := (38299 / 961701)) (n := 12)
    (lo := (79690603 / 1000000000)) (hi := (19922651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461701) = 1/(461701 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_303 : Bounds (-19922651 / 250000000) (-79690603 / 1000000000) (Real.log (461701 / 500000)) := by
  have h := reflection_log_303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_304_neg : (5884533 / 1000000000) ≤ -Real.log (248533186599 / 250000000000) ∧
    -Real.log (248533186599 / 250000000000) ≤ (2942267 / 500000000) := by
  have h := checkLog_sound (w := (1466813401 / 498533186599)) (n := 12)
    (lo := (5884533 / 1000000000)) (hi := (2942267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248533186599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248533186599) = 1/(248533186599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_304 : Bounds (-2942267 / 500000000) (-5884533 / 1000000000) (Real.log (248533186599 / 250000000000)) := by
  have h := reflection_log_304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_305_neg : (5853139 / 1000000000) ≤ -Real.log (248540989191 / 250000000000) ∧
    -Real.log (248540989191 / 250000000000) ≤ (292657 / 50000000) := by
  have h := checkLog_sound (w := (1459010809 / 498540989191)) (n := 12)
    (lo := (5853139 / 1000000000)) (hi := (292657 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248540989191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248540989191) = 1/(248540989191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_305 : Bounds (-292657 / 50000000) (-5853139 / 1000000000) (Real.log (248540989191 / 250000000000)) := by
  have h := reflection_log_305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_306_neg : (15308627 / 100000000) ≤ -Real.log (50000000000 / 58271275847) ∧
    -Real.log (50000000000 / 58271275847) ≤ (153086271 / 1000000000) := by
  have h := checkLog_sound (w := (8271275847 / 108271275847)) (n := 12)
    (lo := (15308627 / 100000000)) (hi := (153086271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58271275847 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58271275847 / 50000000000) = 1/(50000000000 / 58271275847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_306 : Bounds (15308627 / 100000000) (153086271 / 1000000000) (Real.log (58271275847 / 50000000000)) := by
  have h := reflection_log_306_neg
  have he : Real.log (58271275847 / 50000000000) = -Real.log (50000000000 / 58271275847) := by
    rw [show ((58271275847 / 50000000000) : ℝ) = ((50000000000 / 58271275847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_307_neg : (4796771 / 31250000) ≤ -Real.log (250000000000 / 291475976877) ∧
    -Real.log (250000000000 / 291475976877) ≤ (153496673 / 1000000000) := by
  have h := checkLog_sound (w := (41475976877 / 541475976877)) (n := 12)
    (lo := (4796771 / 31250000)) (hi := (153496673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291475976877 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291475976877 / 250000000000) = 1/(250000000000 / 291475976877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_307 : Bounds (4796771 / 31250000) (153496673 / 1000000000) (Real.log (291475976877 / 250000000000)) := by
  have h := reflection_log_307_neg
  have he : Real.log (291475976877 / 250000000000) = -Real.log (250000000000 / 291475976877) := by
    rw [show ((291475976877 / 250000000000) : ℝ) = ((250000000000 / 291475976877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_308_neg : (38373553 / 125000000) ≤ -Real.log (500000000000 / 679662616491) ∧
    -Real.log (500000000000 / 679662616491) ≤ (12279537 / 40000000) := by
  have h := checkLog_sound (w := (179662616491 / 1179662616491)) (n := 12)
    (lo := (38373553 / 125000000)) (hi := (12279537 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679662616491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679662616491 / 500000000000) = 1/(500000000000 / 679662616491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_308 : Bounds (38373553 / 125000000) (12279537 / 40000000) (Real.log (679662616491 / 500000000000)) := by
  have h := reflection_log_308_neg
  have he : Real.log (679662616491 / 500000000000) = -Real.log (500000000000 / 679662616491) := by
    rw [show ((679662616491 / 500000000000) : ℝ) = ((500000000000 / 679662616491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_309_neg : (38399147 / 125000000) ≤ -Real.log (500000000000 / 679801793299) ∧
    -Real.log (500000000000 / 679801793299) ≤ (307193177 / 1000000000) := by
  have h := checkLog_sound (w := (179801793299 / 1179801793299)) (n := 12)
    (lo := (38399147 / 125000000)) (hi := (307193177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679801793299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679801793299 / 500000000000) = 1/(500000000000 / 679801793299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_309 : Bounds (38399147 / 125000000) (307193177 / 1000000000) (Real.log (679801793299 / 500000000000)) := by
  have h := reflection_log_309_neg
  have he : Real.log (679801793299 / 500000000000) = -Real.log (500000000000 / 679801793299) := by
    rw [show ((679801793299 / 500000000000) : ℝ) = ((500000000000 / 679801793299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_310_neg : (28386699 / 200000000) ≤ -Real.log (400 / 461) ∧
    -Real.log (400 / 461) ≤ (17741687 / 125000000) := by
  have h := checkLog_sound (w := (61 / 861)) (n := 12)
    (lo := (28386699 / 200000000)) (hi := (17741687 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461 / 400) = 1/(400 / 461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_310 : Bounds (28386699 / 200000000) (17741687 / 125000000) (Real.log (461 / 400)) := by
  have h := reflection_log_310_neg
  have he : Real.log (461 / 400) = -Real.log (400 / 461) := by
    rw [show ((461 / 400) : ℝ) = ((400 / 461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_311_neg : (165464439 / 1000000000) ≤ -Real.log (339 / 400) ∧
    -Real.log (339 / 400) ≤ (4136611 / 25000000) := by
  have h := checkLog_sound (w := (61 / 739)) (n := 12)
    (lo := (165464439 / 1000000000)) (hi := (4136611 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 339) = 1/(339 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_311 : Bounds (-4136611 / 25000000) (-165464439 / 1000000000) (Real.log (339 / 400)) := by
  have h := reflection_log_311_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_312_neg : (19061 / 125000000) ≤ -Real.log (400000 / 400061) ∧
    -Real.log (400000 / 400061) ≤ (152489 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 800061)) (n := 12)
    (lo := (19061 / 125000000)) (hi := (152489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400061 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400061 / 400000) = 1/(400000 / 400061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_312 : Bounds (19061 / 125000000) (152489 / 1000000000) (Real.log (400061 / 400000)) := by
  have h := reflection_log_312_neg
  have he : Real.log (400061 / 400000) = -Real.log (400000 / 400061) := by
    rw [show ((400061 / 400000) : ℝ) = ((400000 / 400061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_313_neg : (152511 / 1000000000) ≤ -Real.log (399939 / 400000) ∧
    -Real.log (399939 / 400000) ≤ (2383 / 15625000) := by
  have h := checkLog_sound (w := (61 / 799939)) (n := 12)
    (lo := (152511 / 1000000000)) (hi := (2383 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399939) = 1/(399939 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_313 : Bounds (-2383 / 15625000) (-152511 / 1000000000) (Real.log (399939 / 400000)) := by
  have h := reflection_log_313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_314_neg : (14732789 / 200000000) ≤ -Real.log (200000 / 215289) ∧
    -Real.log (200000 / 215289) ≤ (36831973 / 500000000) := by
  have h := checkLog_sound (w := (15289 / 415289)) (n := 12)
    (lo := (14732789 / 200000000)) (hi := (36831973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215289 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215289 / 200000) = 1/(200000 / 215289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_314 : Bounds (14732789 / 200000000) (36831973 / 500000000) (Real.log (215289 / 200000)) := by
  have h := reflection_log_314_neg
  have he : Real.log (215289 / 200000) = -Real.log (200000 / 215289) := by
    rw [show ((215289 / 200000) : ℝ) = ((200000 / 215289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_315_neg : (3180997 / 40000000) ≤ -Real.log (184711 / 200000) ∧
    -Real.log (184711 / 200000) ≤ (39762463 / 500000000) := by
  have h := checkLog_sound (w := (15289 / 384711)) (n := 12)
    (lo := (3180997 / 40000000)) (hi := (39762463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184711) = 1/(184711 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_315 : Bounds (-39762463 / 500000000) (-3180997 / 40000000) (Real.log (184711 / 200000)) := by
  have h := reflection_log_315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_316_neg : (7385251 / 100000000) ≤ -Real.log (125000 / 134581) ∧
    -Real.log (125000 / 134581) ≤ (73852511 / 1000000000) := by
  have h := checkLog_sound (w := (9581 / 259581)) (n := 12)
    (lo := (7385251 / 100000000)) (hi := (73852511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134581 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134581 / 125000) = 1/(125000 / 134581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_316 : Bounds (7385251 / 100000000) (73852511 / 1000000000) (Real.log (134581 / 125000)) := by
  have h := reflection_log_316_neg
  have he : Real.log (134581 / 125000) = -Real.log (125000 / 134581) := by
    rw [show ((134581 / 125000) : ℝ) = ((125000 / 134581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_317_neg : (4984047 / 62500000) ≤ -Real.log (115419 / 125000) ∧
    -Real.log (115419 / 125000) ≤ (79744753 / 1000000000) := by
  have h := checkLog_sound (w := (9581 / 240419)) (n := 12)
    (lo := (4984047 / 62500000)) (hi := (79744753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115419) = 1/(115419 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_317 : Bounds (-79744753 / 1000000000) (-4984047 / 62500000) (Real.log (115419 / 125000)) := by
  have h := reflection_log_317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_318_neg : (5892241 / 1000000000) ≤ -Real.log (15533204439 / 15625000000) ∧
    -Real.log (15533204439 / 15625000000) ≤ (2946121 / 500000000) := by
  have h := checkLog_sound (w := (91795561 / 31158204439)) (n := 12)
    (lo := (5892241 / 1000000000)) (hi := (2946121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15533204439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15533204439) = 1/(15533204439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_318 : Bounds (-2946121 / 500000000) (-5892241 / 1000000000) (Real.log (15533204439 / 15625000000)) := by
  have h := reflection_log_318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_319_neg : (293049 / 50000000) ≤ -Real.log (39766246479 / 40000000000) ∧
    -Real.log (39766246479 / 40000000000) ≤ (5860981 / 1000000000) := by
  have h := checkLog_sound (w := (233753521 / 79766246479)) (n := 12)
    (lo := (293049 / 50000000)) (hi := (5860981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39766246479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39766246479) = 1/(39766246479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_319 : Bounds (-5860981 / 1000000000) (-293049 / 50000000) (Real.log (39766246479 / 40000000000)) := by
  have h := reflection_log_319_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0005 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_320_neg : (15318887 / 100000000) ≤ -Real.log (62500000000 / 72846568423) ∧
    -Real.log (62500000000 / 72846568423) ≤ (153188871 / 1000000000) := by
  have h := checkLog_sound (w := (10346568423 / 135346568423)) (n := 12)
    (lo := (15318887 / 100000000)) (hi := (153188871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72846568423 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72846568423 / 62500000000) = 1/(62500000000 / 72846568423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_320 : Bounds (15318887 / 100000000) (153188871 / 1000000000) (Real.log (72846568423 / 62500000000)) := by
  have h := reflection_log_320_neg
  have he : Real.log (72846568423 / 62500000000) = -Real.log (62500000000 / 72846568423) := by
    rw [show ((72846568423 / 62500000000) : ℝ) = ((62500000000 / 72846568423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_321_neg : (153597263 / 1000000000) ≤ -Real.log (31250000000 / 36438162261) ∧
    -Real.log (31250000000 / 36438162261) ≤ (9599829 / 62500000) := by
  have h := checkLog_sound (w := (5188162261 / 67688162261)) (n := 12)
    (lo := (153597263 / 1000000000)) (hi := (9599829 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36438162261 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36438162261 / 31250000000) = 1/(31250000000 / 36438162261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_321 : Bounds (153597263 / 1000000000) (9599829 / 62500000) (Real.log (36438162261 / 31250000000)) := by
  have h := reflection_log_321_neg
  have he : Real.log (36438162261 / 31250000000) = -Real.log (31250000000 / 36438162261) := by
    rw [show ((36438162261 / 31250000000) : ℝ) = ((31250000000 / 36438162261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_322_neg : (38399147 / 125000000) ≤ -Real.log (250000000000 / 339900896649) ∧
    -Real.log (250000000000 / 339900896649) ≤ (307193177 / 1000000000) := by
  have h := checkLog_sound (w := (89900896649 / 589900896649)) (n := 12)
    (lo := (38399147 / 125000000)) (hi := (307193177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339900896649 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339900896649 / 250000000000) = 1/(250000000000 / 339900896649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_322 : Bounds (38399147 / 125000000) (307193177 / 1000000000) (Real.log (339900896649 / 250000000000)) := by
  have h := reflection_log_322_neg
  have he : Real.log (339900896649 / 250000000000) = -Real.log (250000000000 / 339900896649) := by
    rw [show ((339900896649 / 250000000000) : ℝ) = ((250000000000 / 339900896649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_323_neg : (61479587 / 200000000) ≤ -Real.log (10000000000 / 13598820059) ∧
    -Real.log (10000000000 / 13598820059) ≤ (19212371 / 62500000) := by
  have h := checkLog_sound (w := (3598820059 / 23598820059)) (n := 12)
    (lo := (61479587 / 200000000)) (hi := (19212371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13598820059 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13598820059 / 10000000000) = 1/(10000000000 / 13598820059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_323 : Bounds (61479587 / 200000000) (19212371 / 62500000) (Real.log (13598820059 / 10000000000)) := by
  have h := reflection_log_323_neg
  have he : Real.log (13598820059 / 10000000000) = -Real.log (10000000000 / 13598820059) := by
    rw [show ((13598820059 / 10000000000) : ℝ) = ((10000000000 / 13598820059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_324_neg : (7101013 / 50000000) ≤ -Real.log (5000 / 5763) ∧
    -Real.log (5000 / 5763) ≤ (142020261 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 10763)) (n := 12)
    (lo := (7101013 / 50000000)) (hi := (142020261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5763 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5763 / 5000) = 1/(5000 / 5763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_324 : Bounds (7101013 / 50000000) (142020261 / 1000000000) (Real.log (5763 / 5000)) := by
  have h := reflection_log_324_neg
  have he : Real.log (5763 / 5000) = -Real.log (5000 / 5763) := by
    rw [show ((5763 / 5000) : ℝ) = ((5000 / 5763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_325_neg : (4139561 / 25000000) ≤ -Real.log (4237 / 5000) ∧
    -Real.log (4237 / 5000) ≤ (165582441 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 9237)) (n := 12)
    (lo := (4139561 / 25000000)) (hi := (165582441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4237) = 1/(4237 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_325 : Bounds (-165582441 / 1000000000) (-4139561 / 25000000) (Real.log (4237 / 5000)) := by
  have h := reflection_log_325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_326_neg : (38147 / 250000000) ≤ -Real.log (5000000 / 5000763) ∧
    -Real.log (5000000 / 5000763) ≤ (152589 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 10000763)) (n := 12)
    (lo := (38147 / 250000000)) (hi := (152589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000763 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000763 / 5000000) = 1/(5000000 / 5000763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_326 : Bounds (38147 / 250000000) (152589 / 1000000000) (Real.log (5000763 / 5000000)) := by
  have h := reflection_log_326_neg
  have he : Real.log (5000763 / 5000000) = -Real.log (5000000 / 5000763) := by
    rw [show ((5000763 / 5000000) : ℝ) = ((5000000 / 5000763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_327_neg : (152611 / 1000000000) ≤ -Real.log (4999237 / 5000000) ∧
    -Real.log (4999237 / 5000000) ≤ (38153 / 250000000) := by
  have h := checkLog_sound (w := (763 / 9999237)) (n := 12)
    (lo := (152611 / 1000000000)) (hi := (38153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999237) = 1/(4999237 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_327 : Bounds (-38153 / 250000000) (-152611 / 1000000000) (Real.log (4999237 / 5000000)) := by
  have h := reflection_log_327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_328_neg : (73899879 / 1000000000) ≤ -Real.log (1000000 / 1076699) ∧
    -Real.log (1000000 / 1076699) ≤ (1847497 / 25000000) := by
  have h := checkLog_sound (w := (76699 / 2076699)) (n := 12)
    (lo := (73899879 / 1000000000)) (hi := (1847497 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076699 / 1000000) = 1/(1000000 / 1076699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_328 : Bounds (73899879 / 1000000000) (1847497 / 25000000) (Real.log (1076699 / 1000000)) := by
  have h := reflection_log_328_neg
  have he : Real.log (1076699 / 1000000) = -Real.log (1000000 / 1076699) := by
    rw [show ((1076699 / 1000000) : ℝ) = ((1000000 / 1076699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_329_neg : (79799987 / 1000000000) ≤ -Real.log (923301 / 1000000) ∧
    -Real.log (923301 / 1000000) ≤ (19949997 / 250000000) := by
  have h := checkLog_sound (w := (76699 / 1923301)) (n := 12)
    (lo := (79799987 / 1000000000)) (hi := (19949997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923301) = 1/(923301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_329 : Bounds (-19949997 / 250000000) (-79799987 / 1000000000) (Real.log (923301 / 1000000)) := by
  have h := reflection_log_329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_330_neg : (1475027 / 250000000) ≤ -Real.log (994117263399 / 1000000000000) ∧
    -Real.log (994117263399 / 1000000000000) ≤ (5900109 / 1000000000) := by
  have h := checkLog_sound (w := (5882736601 / 1994117263399)) (n := 12)
    (lo := (1475027 / 250000000)) (hi := (5900109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994117263399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994117263399) = 1/(994117263399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_330 : Bounds (-5900109 / 1000000000) (-1475027 / 250000000) (Real.log (994117263399 / 1000000000000)) := by
  have h := reflection_log_330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_331_neg : (15329147 / 100000000) ≤ -Real.log (250000000000 / 291416171451) ∧
    -Real.log (250000000000 / 291416171451) ≤ (153291471 / 1000000000) := by
  have h := checkLog_sound (w := (41416171451 / 541416171451)) (n := 12)
    (lo := (15329147 / 100000000)) (hi := (153291471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291416171451 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291416171451 / 250000000000) = 1/(250000000000 / 291416171451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_331 : Bounds (15329147 / 100000000) (153291471 / 1000000000) (Real.log (291416171451 / 250000000000)) := by
  have h := reflection_log_331_neg
  have he : Real.log (291416171451 / 250000000000) = -Real.log (250000000000 / 291416171451) := by
    rw [show ((291416171451 / 250000000000) : ℝ) = ((250000000000 / 291416171451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_332_neg : (76849933 / 500000000) ≤ -Real.log (50000000000 / 58307041799) ∧
    -Real.log (50000000000 / 58307041799) ≤ (153699867 / 1000000000) := by
  have h := checkLog_sound (w := (8307041799 / 108307041799)) (n := 12)
    (lo := (76849933 / 500000000)) (hi := (153699867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58307041799 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58307041799 / 50000000000) = 1/(50000000000 / 58307041799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_332 : Bounds (76849933 / 500000000) (153699867 / 1000000000) (Real.log (58307041799 / 50000000000)) := by
  have h := reflection_log_332_neg
  have he : Real.log (58307041799 / 50000000000) = -Real.log (50000000000 / 58307041799) := by
    rw [show ((58307041799 / 50000000000) : ℝ) = ((50000000000 / 58307041799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_333_neg : (61479587 / 200000000) ≤ -Real.log (500000000000 / 679941002949) ∧
    -Real.log (500000000000 / 679941002949) ≤ (19212371 / 62500000) := by
  have h := checkLog_sound (w := (179941002949 / 1179941002949)) (n := 12)
    (lo := (61479587 / 200000000)) (hi := (19212371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679941002949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679941002949 / 500000000000) = 1/(500000000000 / 679941002949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_333 : Bounds (61479587 / 200000000) (19212371 / 62500000) (Real.log (679941002949 / 500000000000)) := by
  have h := reflection_log_333_neg
  have he : Real.log (679941002949 / 500000000000) = -Real.log (500000000000 / 679941002949) := by
    rw [show ((679941002949 / 500000000000) : ℝ) = ((500000000000 / 679941002949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_334_neg : (3076027 / 10000000) ≤ -Real.log (500000000000 / 680080245457) ∧
    -Real.log (500000000000 / 680080245457) ≤ (307602701 / 1000000000) := by
  have h := checkLog_sound (w := (180080245457 / 1180080245457)) (n := 12)
    (lo := (3076027 / 10000000)) (hi := (307602701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680080245457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680080245457 / 500000000000) = 1/(500000000000 / 680080245457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_334 : Bounds (3076027 / 10000000) (307602701 / 1000000000) (Real.log (680080245457 / 500000000000)) := by
  have h := reflection_log_334_neg
  have he : Real.log (680080245457 / 500000000000) = -Real.log (500000000000 / 680080245457) := by
    rw [show ((680080245457 / 500000000000) : ℝ) = ((500000000000 / 680080245457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_335_neg : (17763377 / 125000000) ≤ -Real.log (10000 / 11527) ∧
    -Real.log (10000 / 11527) ≤ (142107017 / 1000000000) := by
  have h := checkLog_sound (w := (1527 / 21527)) (n := 12)
    (lo := (17763377 / 125000000)) (hi := (142107017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11527 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11527 / 10000) = 1/(10000 / 11527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_335 : Bounds (17763377 / 125000000) (142107017 / 1000000000) (Real.log (11527 / 10000)) := by
  have h := reflection_log_335_neg
  have he : Real.log (11527 / 10000) = -Real.log (10000 / 11527) := by
    rw [show ((11527 / 10000) : ℝ) = ((10000 / 11527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_336_neg : (33140091 / 200000000) ≤ -Real.log (8473 / 10000) ∧
    -Real.log (8473 / 10000) ≤ (20712557 / 125000000) := by
  have h := checkLog_sound (w := (1527 / 18473)) (n := 12)
    (lo := (33140091 / 200000000)) (hi := (20712557 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8473) = 1/(8473 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_336 : Bounds (-20712557 / 125000000) (-33140091 / 200000000) (Real.log (8473 / 10000)) := by
  have h := reflection_log_336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_337_neg : (9543 / 62500000) ≤ -Real.log (10000000 / 10001527) ∧
    -Real.log (10000000 / 10001527) ≤ (152689 / 1000000000) := by
  have h := checkLog_sound (w := (1527 / 20001527)) (n := 12)
    (lo := (9543 / 62500000)) (hi := (152689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001527 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001527 / 10000000) = 1/(10000000 / 10001527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_337 : Bounds (9543 / 62500000) (152689 / 1000000000) (Real.log (10001527 / 10000000)) := by
  have h := reflection_log_337_neg
  have he : Real.log (10001527 / 10000000) = -Real.log (10000000 / 10001527) := by
    rw [show ((10001527 / 10000000) : ℝ) = ((10000000 / 10001527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_338_neg : (152711 / 1000000000) ≤ -Real.log (9998473 / 10000000) ∧
    -Real.log (9998473 / 10000000) ≤ (19089 / 125000000) := by
  have h := checkLog_sound (w := (1527 / 19998473)) (n := 12)
    (lo := (152711 / 1000000000)) (hi := (19089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998473) = 1/(9998473 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_338 : Bounds (-19089 / 125000000) (-152711 / 1000000000) (Real.log (9998473 / 10000000)) := by
  have h := reflection_log_338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_339_neg : (73757767 / 1000000000) ≤ -Real.log (500000 / 538273) ∧
    -Real.log (500000 / 538273) ≤ (9219721 / 125000000) := by
  have h := checkLog_sound (w := (38273 / 1038273)) (n := 12)
    (lo := (73757767 / 1000000000)) (hi := (9219721 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538273 / 500000) = 1/(500000 / 538273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_339 : Bounds (73757767 / 1000000000) (9219721 / 125000000) (Real.log (538273 / 500000)) := by
  have h := reflection_log_339_neg
  have he : Real.log (538273 / 500000) = -Real.log (500000 / 538273) := by
    rw [show ((538273 / 500000) : ℝ) = ((500000 / 538273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_340_neg : (79634291 / 1000000000) ≤ -Real.log (461727 / 500000) ∧
    -Real.log (461727 / 500000) ≤ (19908573 / 250000000) := by
  have h := checkLog_sound (w := (38273 / 961727)) (n := 12)
    (lo := (79634291 / 1000000000)) (hi := (19908573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461727) = 1/(461727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_340 : Bounds (-19908573 / 250000000) (-79634291 / 1000000000) (Real.log (461727 / 500000)) := by
  have h := reflection_log_340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_341_neg : (18486811 / 250000000) ≤ -Real.log (4000 / 4307) ∧
    -Real.log (4000 / 4307) ≤ (14789449 / 200000000) := by
  have h := checkLog_sound (w := (307 / 8307)) (n := 12)
    (lo := (18486811 / 250000000)) (hi := (14789449 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4307 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4307 / 4000) = 1/(4000 / 4307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_341 : Bounds (18486811 / 250000000) (14789449 / 200000000) (Real.log (4307 / 4000)) := by
  have h := reflection_log_341_neg
  have he : Real.log (4307 / 4000) = -Real.log (4000 / 4307) := by
    rw [show ((4307 / 4000) : ℝ) = ((4000 / 4307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_342_neg : (3194209 / 40000000) ≤ -Real.log (3693 / 4000) ∧
    -Real.log (3693 / 4000) ≤ (39927613 / 500000000) := by
  have h := checkLog_sound (w := (307 / 7693)) (n := 12)
    (lo := (3194209 / 40000000)) (hi := (39927613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3693) = 1/(3693 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_342 : Bounds (-39927613 / 500000000) (-3194209 / 40000000) (Real.log (3693 / 4000)) := by
  have h := reflection_log_342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_343_neg : (295399 / 50000000) ≤ -Real.log (15905751 / 16000000) ∧
    -Real.log (15905751 / 16000000) ≤ (5907981 / 1000000000) := by
  have h := checkLog_sound (w := (94249 / 31905751)) (n := 12)
    (lo := (295399 / 50000000)) (hi := (5907981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15905751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15905751) = 1/(15905751 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_343 : Bounds (-5907981 / 1000000000) (-295399 / 50000000) (Real.log (15905751 / 16000000)) := by
  have h := reflection_log_343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_344_neg : (5876523 / 1000000000) ≤ -Real.log (248535177471 / 250000000000) ∧
    -Real.log (248535177471 / 250000000000) ≤ (1469131 / 250000000) := by
  have h := checkLog_sound (w := (1464822529 / 498535177471)) (n := 12)
    (lo := (5876523 / 1000000000)) (hi := (1469131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248535177471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248535177471) = 1/(248535177471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_344 : Bounds (-1469131 / 250000000) (-5876523 / 1000000000) (Real.log (248535177471 / 250000000000)) := by
  have h := reflection_log_344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_345_neg : (153392059 / 1000000000) ≤ -Real.log (500000000000 / 582890972371) ∧
    -Real.log (500000000000 / 582890972371) ≤ (7669603 / 50000000) := by
  have h := checkLog_sound (w := (82890972371 / 1082890972371)) (n := 12)
    (lo := (153392059 / 1000000000)) (hi := (7669603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582890972371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582890972371 / 500000000000) = 1/(500000000000 / 582890972371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_345 : Bounds (153392059 / 1000000000) (7669603 / 50000000) (Real.log (582890972371 / 500000000000)) := by
  have h := reflection_log_345_neg
  have he : Real.log (582890972371 / 500000000000) = -Real.log (500000000000 / 582890972371) := by
    rw [show ((582890972371 / 500000000000) : ℝ) = ((500000000000 / 582890972371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_346_neg : (15380247 / 100000000) ≤ -Real.log (500000000000 / 583130246413) ∧
    -Real.log (500000000000 / 583130246413) ≤ (153802471 / 1000000000) := by
  have h := checkLog_sound (w := (83130246413 / 1083130246413)) (n := 12)
    (lo := (15380247 / 100000000)) (hi := (153802471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583130246413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583130246413 / 500000000000) = 1/(500000000000 / 583130246413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_346 : Bounds (15380247 / 100000000) (153802471 / 1000000000) (Real.log (583130246413 / 500000000000)) := by
  have h := reflection_log_346_neg
  have he : Real.log (583130246413 / 500000000000) = -Real.log (500000000000 / 583130246413) := by
    rw [show ((583130246413 / 500000000000) : ℝ) = ((500000000000 / 583130246413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_347_neg : (3076027 / 10000000) ≤ -Real.log (31250000000 / 42505015341) ∧
    -Real.log (31250000000 / 42505015341) ≤ (307602701 / 1000000000) := by
  have h := checkLog_sound (w := (11255015341 / 73755015341)) (n := 12)
    (lo := (3076027 / 10000000)) (hi := (307602701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42505015341 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42505015341 / 31250000000) = 1/(31250000000 / 42505015341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_347 : Bounds (3076027 / 10000000) (307602701 / 1000000000) (Real.log (42505015341 / 31250000000)) := by
  have h := reflection_log_347_neg
  have he : Real.log (42505015341 / 31250000000) = -Real.log (31250000000 / 42505015341) := by
    rw [show ((42505015341 / 31250000000) : ℝ) = ((31250000000 / 42505015341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_348_neg : (19237967 / 62500000) ≤ -Real.log (500000000000 / 680219520831) ∧
    -Real.log (500000000000 / 680219520831) ≤ (307807473 / 1000000000) := by
  have h := checkLog_sound (w := (180219520831 / 1180219520831)) (n := 12)
    (lo := (19237967 / 62500000)) (hi := (307807473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680219520831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680219520831 / 500000000000) = 1/(500000000000 / 680219520831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_348 : Bounds (19237967 / 62500000) (307807473 / 1000000000) (Real.log (680219520831 / 500000000000)) := by
  have h := reflection_log_348_neg
  have he : Real.log (680219520831 / 500000000000) = -Real.log (500000000000 / 680219520831) := by
    rw [show ((680219520831 / 500000000000) : ℝ) = ((500000000000 / 680219520831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_349_neg : (28438753 / 200000000) ≤ -Real.log (1250 / 1441) ∧
    -Real.log (1250 / 1441) ≤ (71096883 / 500000000) := by
  have h := checkLog_sound (w := (191 / 2691)) (n := 12)
    (lo := (28438753 / 200000000)) (hi := (71096883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441 / 1250) = 1/(1250 / 1441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_349 : Bounds (28438753 / 200000000) (71096883 / 500000000) (Real.log (1441 / 1250)) := by
  have h := reflection_log_349_neg
  have he : Real.log (1441 / 1250) = -Real.log (1250 / 1441) := by
    rw [show ((1441 / 1250) : ℝ) = ((1250 / 1441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_350_neg : (41454621 / 250000000) ≤ -Real.log (1059 / 1250) ∧
    -Real.log (1059 / 1250) ≤ (33163697 / 200000000) := by
  have h := checkLog_sound (w := (191 / 2309)) (n := 12)
    (lo := (41454621 / 250000000)) (hi := (33163697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1059) = 1/(1059 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_350 : Bounds (-33163697 / 200000000) (-41454621 / 250000000) (Real.log (1059 / 1250)) := by
  have h := reflection_log_350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_351_neg : (38197 / 250000000) ≤ -Real.log (1250000 / 1250191) ∧
    -Real.log (1250000 / 1250191) ≤ (152789 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 2500191)) (n := 12)
    (lo := (38197 / 250000000)) (hi := (152789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250191 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250191 / 1250000) = 1/(1250000 / 1250191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_351 : Bounds (38197 / 250000000) (152789 / 1000000000) (Real.log (1250191 / 1250000)) := by
  have h := reflection_log_351_neg
  have he : Real.log (1250191 / 1250000) = -Real.log (1250000 / 1250191) := by
    rw [show ((1250191 / 1250000) : ℝ) = ((1250000 / 1250191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_352_neg : (152811 / 1000000000) ≤ -Real.log (1249809 / 1250000) ∧
    -Real.log (1249809 / 1250000) ≤ (38203 / 250000000) := by
  have h := checkLog_sound (w := (191 / 2499809)) (n := 12)
    (lo := (152811 / 1000000000)) (hi := (38203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249809) = 1/(1249809 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_352 : Bounds (-38203 / 250000000) (-152811 / 1000000000) (Real.log (1249809 / 1250000)) := by
  have h := reflection_log_352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_353_neg : (3690257 / 50000000) ≤ -Real.log (1000000 / 1076597) ∧
    -Real.log (1000000 / 1076597) ≤ (73805141 / 1000000000) := by
  have h := checkLog_sound (w := (76597 / 2076597)) (n := 12)
    (lo := (3690257 / 50000000)) (hi := (73805141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076597 / 1000000) = 1/(1000000 / 1076597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_353 : Bounds (3690257 / 50000000) (73805141 / 1000000000) (Real.log (1076597 / 1000000)) := by
  have h := reflection_log_353_neg
  have he : Real.log (1076597 / 1000000) = -Real.log (1000000 / 1076597) := by
    rw [show ((1076597 / 1000000) : ℝ) = ((1000000 / 1076597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_354_neg : (996119 / 12500000) ≤ -Real.log (923403 / 1000000) ∧
    -Real.log (923403 / 1000000) ≤ (79689521 / 1000000000) := by
  have h := checkLog_sound (w := (76597 / 1923403)) (n := 12)
    (lo := (996119 / 12500000)) (hi := (79689521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923403) = 1/(923403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_354 : Bounds (-79689521 / 1000000000) (-996119 / 12500000) (Real.log (923403 / 1000000)) := by
  have h := reflection_log_354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_355_neg : (73993679 / 1000000000) ≤ -Real.log (625 / 673) ∧
    -Real.log (625 / 673) ≤ (924921 / 12500000) := by
  have h := checkLog_sound (w := (24 / 649)) (n := 12)
    (lo := (73993679 / 1000000000)) (hi := (924921 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673 / 625) = 1/(625 / 673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_355 : Bounds (73993679 / 1000000000) (924921 / 12500000) (Real.log (673 / 625)) := by
  have h := reflection_log_355_neg
  have he : Real.log (673 / 625) = -Real.log (625 / 673) := by
    rw [show ((673 / 625) : ℝ) = ((625 / 673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_356_neg : (79909383 / 1000000000) ≤ -Real.log (577 / 625) ∧
    -Real.log (577 / 625) ≤ (9988673 / 125000000) := by
  have h := checkLog_sound (w := (24 / 601)) (n := 12)
    (lo := (79909383 / 1000000000)) (hi := (9988673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 577) = 1/(577 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_356 : Bounds (-9988673 / 125000000) (-79909383 / 1000000000) (Real.log (577 / 625)) := by
  have h := reflection_log_356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_357_neg : (5915703 / 1000000000) ≤ -Real.log (388321 / 390625) ∧
    -Real.log (388321 / 390625) ≤ (739463 / 125000000) := by
  have h := checkLog_sound (w := (1152 / 389473)) (n := 12)
    (lo := (5915703 / 1000000000)) (hi := (739463 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390625 / 388321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390625 / 388321) = 1/(388321 / 390625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_357 : Bounds (-739463 / 125000000) (-5915703 / 1000000000) (Real.log (388321 / 390625)) := by
  have h := reflection_log_357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_358_neg : (5884379 / 1000000000) ≤ -Real.log (994132899591 / 1000000000000) ∧
    -Real.log (994132899591 / 1000000000000) ≤ (294219 / 50000000) := by
  have h := checkLog_sound (w := (5867100409 / 1994132899591)) (n := 12)
    (lo := (5884379 / 1000000000)) (hi := (294219 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994132899591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994132899591) = 1/(994132899591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_358 : Bounds (-294219 / 50000000) (-5884379 / 1000000000) (Real.log (994132899591 / 1000000000000)) := by
  have h := reflection_log_358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_359_neg : (7674733 / 50000000) ≤ -Real.log (500000000000 / 582950780969) ∧
    -Real.log (500000000000 / 582950780969) ≤ (153494661 / 1000000000) := by
  have h := checkLog_sound (w := (82950780969 / 1082950780969)) (n := 12)
    (lo := (7674733 / 50000000)) (hi := (153494661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582950780969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582950780969 / 500000000000) = 1/(500000000000 / 582950780969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_359 : Bounds (7674733 / 50000000) (153494661 / 1000000000) (Real.log (582950780969 / 500000000000)) := by
  have h := reflection_log_359_neg
  have he : Real.log (582950780969 / 500000000000) = -Real.log (500000000000 / 582950780969) := by
    rw [show ((582950780969 / 500000000000) : ℝ) = ((500000000000 / 582950780969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_360_neg : (153903063 / 1000000000) ≤ -Real.log (250000000000 / 291594454073) ∧
    -Real.log (250000000000 / 291594454073) ≤ (19237883 / 125000000) := by
  have h := checkLog_sound (w := (41594454073 / 541594454073)) (n := 12)
    (lo := (153903063 / 1000000000)) (hi := (19237883 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291594454073 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291594454073 / 250000000000) = 1/(250000000000 / 291594454073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_360 : Bounds (153903063 / 1000000000) (19237883 / 125000000) (Real.log (291594454073 / 250000000000)) := by
  have h := reflection_log_360_neg
  have he : Real.log (291594454073 / 250000000000) = -Real.log (250000000000 / 291594454073) := by
    rw [show ((291594454073 / 250000000000) : ℝ) = ((250000000000 / 291594454073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_361_neg : (19237967 / 62500000) ≤ -Real.log (50000000000 / 68021952083) ∧
    -Real.log (50000000000 / 68021952083) ≤ (307807473 / 1000000000) := by
  have h := checkLog_sound (w := (18021952083 / 118021952083)) (n := 12)
    (lo := (19237967 / 62500000)) (hi := (307807473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68021952083 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68021952083 / 50000000000) = 1/(50000000000 / 68021952083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_361 : Bounds (19237967 / 62500000) (307807473 / 1000000000) (Real.log (68021952083 / 50000000000)) := by
  have h := reflection_log_361_neg
  have he : Real.log (68021952083 / 50000000000) = -Real.log (50000000000 / 68021952083) := by
    rw [show ((68021952083 / 50000000000) : ℝ) = ((50000000000 / 68021952083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_362_neg : (1232049 / 4000000) ≤ -Real.log (100000000000 / 136071765817) ∧
    -Real.log (100000000000 / 136071765817) ≤ (308012251 / 1000000000) := by
  have h := checkLog_sound (w := (36071765817 / 236071765817)) (n := 12)
    (lo := (1232049 / 4000000)) (hi := (308012251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136071765817 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136071765817 / 100000000000) = 1/(100000000000 / 136071765817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_362 : Bounds (1232049 / 4000000) (308012251 / 1000000000) (Real.log (136071765817 / 100000000000)) := by
  have h := reflection_log_362_neg
  have he : Real.log (136071765817 / 100000000000) = -Real.log (100000000000 / 136071765817) := by
    rw [show ((136071765817 / 100000000000) : ℝ) = ((100000000000 / 136071765817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_363_neg : (142280507 / 1000000000) ≤ -Real.log (10000 / 11529) ∧
    -Real.log (10000 / 11529) ≤ (35570127 / 250000000) := by
  have h := checkLog_sound (w := (1529 / 21529)) (n := 12)
    (lo := (142280507 / 1000000000)) (hi := (35570127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11529 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11529 / 10000) = 1/(10000 / 11529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_363 : Bounds (142280507 / 1000000000) (35570127 / 250000000) (Real.log (11529 / 10000)) := by
  have h := reflection_log_363_neg
  have he : Real.log (11529 / 10000) = -Real.log (10000 / 11529) := by
    rw [show ((11529 / 10000) : ℝ) = ((10000 / 11529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_364_neg : (165936527 / 1000000000) ≤ -Real.log (8471 / 10000) ∧
    -Real.log (8471 / 10000) ≤ (10371033 / 62500000) := by
  have h := checkLog_sound (w := (1529 / 18471)) (n := 12)
    (lo := (165936527 / 1000000000)) (hi := (10371033 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8471) = 1/(8471 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_364 : Bounds (-10371033 / 62500000) (-165936527 / 1000000000) (Real.log (8471 / 10000)) := by
  have h := reflection_log_364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_365_neg : (19111 / 125000000) ≤ -Real.log (10000000 / 10001529) ∧
    -Real.log (10000000 / 10001529) ≤ (152889 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 20001529)) (n := 12)
    (lo := (19111 / 125000000)) (hi := (152889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001529 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001529 / 10000000) = 1/(10000000 / 10001529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_365 : Bounds (19111 / 125000000) (152889 / 1000000000) (Real.log (10001529 / 10000000)) := by
  have h := reflection_log_365_neg
  have he : Real.log (10001529 / 10000000) = -Real.log (10000000 / 10001529) := by
    rw [show ((10001529 / 10000000) : ℝ) = ((10000000 / 10001529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_366_neg : (152911 / 1000000000) ≤ -Real.log (9998471 / 10000000) ∧
    -Real.log (9998471 / 10000000) ≤ (9557 / 62500000) := by
  have h := checkLog_sound (w := (1529 / 19998471)) (n := 12)
    (lo := (152911 / 1000000000)) (hi := (9557 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998471) = 1/(9998471 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_366 : Bounds (-9557 / 62500000) (-152911 / 1000000000) (Real.log (9998471 / 10000000)) := by
  have h := reflection_log_366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_367_neg : (36925791 / 500000000) ≤ -Real.log (1000000 / 1076647) ∧
    -Real.log (1000000 / 1076647) ≤ (73851583 / 1000000000) := by
  have h := checkLog_sound (w := (76647 / 2076647)) (n := 12)
    (lo := (36925791 / 500000000)) (hi := (73851583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076647 / 1000000) = 1/(1000000 / 1076647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_367 : Bounds (36925791 / 500000000) (73851583 / 1000000000) (Real.log (1076647 / 1000000)) := by
  have h := reflection_log_367_neg
  have he : Real.log (1076647 / 1000000) = -Real.log (1000000 / 1076647) := by
    rw [show ((1076647 / 1000000) : ℝ) = ((1000000 / 1076647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_368_neg : (79743669 / 1000000000) ≤ -Real.log (923353 / 1000000) ∧
    -Real.log (923353 / 1000000) ≤ (7974367 / 100000000) := by
  have h := checkLog_sound (w := (76647 / 1923353)) (n := 12)
    (lo := (79743669 / 1000000000)) (hi := (7974367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923353) = 1/(923353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_368 : Bounds (-7974367 / 100000000) (-79743669 / 1000000000) (Real.log (923353 / 1000000)) := by
  have h := reflection_log_368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_369_neg : (74041041 / 1000000000) ≤ -Real.log (1000000 / 1076851) ∧
    -Real.log (1000000 / 1076851) ≤ (37020521 / 500000000) := by
  have h := checkLog_sound (w := (76851 / 2076851)) (n := 12)
    (lo := (74041041 / 1000000000)) (hi := (37020521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076851 / 1000000) = 1/(1000000 / 1076851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_369 : Bounds (74041041 / 1000000000) (37020521 / 500000000) (Real.log (1076851 / 1000000)) := by
  have h := reflection_log_369_neg
  have he : Real.log (1076851 / 1000000) = -Real.log (1000000 / 1076851) := by
    rw [show ((1076851 / 1000000) : ℝ) = ((1000000 / 1076851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_370_neg : (79964627 / 1000000000) ≤ -Real.log (923149 / 1000000) ∧
    -Real.log (923149 / 1000000) ≤ (19991157 / 250000000) := by
  have h := checkLog_sound (w := (76851 / 1923149)) (n := 12)
    (lo := (79964627 / 1000000000)) (hi := (19991157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923149) = 1/(923149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_370 : Bounds (-19991157 / 250000000) (-79964627 / 1000000000) (Real.log (923149 / 1000000)) := by
  have h := reflection_log_370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_371_neg : (2961793 / 500000000) ≤ -Real.log (994093923799 / 1000000000000) ∧
    -Real.log (994093923799 / 1000000000000) ≤ (5923587 / 1000000000) := by
  have h := checkLog_sound (w := (5906076201 / 1994093923799)) (n := 12)
    (lo := (2961793 / 500000000)) (hi := (5923587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994093923799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994093923799) = 1/(994093923799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_371 : Bounds (-5923587 / 1000000000) (-2961793 / 500000000) (Real.log (994093923799 / 1000000000000)) := by
  have h := reflection_log_371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_372_neg : (2946043 / 500000000) ≤ -Real.log (994125237391 / 1000000000000) ∧
    -Real.log (994125237391 / 1000000000000) ≤ (5892087 / 1000000000) := by
  have h := checkLog_sound (w := (5874762609 / 1994125237391)) (n := 12)
    (lo := (2946043 / 500000000)) (hi := (5892087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994125237391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994125237391) = 1/(994125237391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_372 : Bounds (-5892087 / 1000000000) (-2946043 / 500000000) (Real.log (994125237391 / 1000000000000)) := by
  have h := reflection_log_372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_373_neg : (153595251 / 1000000000) ≤ -Real.log (15625000000 / 18219044477) ∧
    -Real.log (15625000000 / 18219044477) ≤ (38398813 / 250000000) := by
  have h := checkLog_sound (w := (2594044477 / 33844044477)) (n := 12)
    (lo := (153595251 / 1000000000)) (hi := (38398813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18219044477 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18219044477 / 15625000000) = 1/(15625000000 / 18219044477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_373 : Bounds (153595251 / 1000000000) (38398813 / 250000000) (Real.log (18219044477 / 15625000000)) := by
  have h := reflection_log_373_neg
  have he : Real.log (18219044477 / 15625000000) = -Real.log (15625000000 / 18219044477) := by
    rw [show ((18219044477 / 15625000000) : ℝ) = ((15625000000 / 18219044477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_374_neg : (38501417 / 250000000) ≤ -Real.log (500000000000 / 583248749661) ∧
    -Real.log (500000000000 / 583248749661) ≤ (154005669 / 1000000000) := by
  have h := checkLog_sound (w := (83248749661 / 1083248749661)) (n := 12)
    (lo := (38501417 / 250000000)) (hi := (154005669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583248749661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583248749661 / 500000000000) = 1/(500000000000 / 583248749661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_374 : Bounds (38501417 / 250000000) (154005669 / 1000000000) (Real.log (583248749661 / 500000000000)) := by
  have h := reflection_log_374_neg
  have he : Real.log (583248749661 / 500000000000) = -Real.log (500000000000 / 583248749661) := by
    rw [show ((583248749661 / 500000000000) : ℝ) = ((500000000000 / 583248749661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_375_neg : (1232049 / 4000000) ≤ -Real.log (125000000000 / 170089707271) ∧
    -Real.log (125000000000 / 170089707271) ≤ (308012251 / 1000000000) := by
  have h := checkLog_sound (w := (45089707271 / 295089707271)) (n := 12)
    (lo := (1232049 / 4000000)) (hi := (308012251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170089707271 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170089707271 / 125000000000) = 1/(125000000000 / 170089707271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_375 : Bounds (1232049 / 4000000) (308012251 / 1000000000) (Real.log (170089707271 / 125000000000)) := by
  have h := reflection_log_375_neg
  have he : Real.log (170089707271 / 125000000000) = -Real.log (125000000000 / 170089707271) := by
    rw [show ((170089707271 / 125000000000) : ℝ) = ((125000000000 / 170089707271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_376_neg : (154108517 / 500000000) ≤ -Real.log (125000000000 / 170124542557) ∧
    -Real.log (125000000000 / 170124542557) ≤ (61643407 / 200000000) := by
  have h := checkLog_sound (w := (45124542557 / 295124542557)) (n := 12)
    (lo := (154108517 / 500000000)) (hi := (61643407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170124542557 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170124542557 / 125000000000) = 1/(125000000000 / 170124542557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_376 : Bounds (154108517 / 500000000) (61643407 / 200000000) (Real.log (170124542557 / 125000000000)) := by
  have h := reflection_log_376_neg
  have he : Real.log (170124542557 / 125000000000) = -Real.log (125000000000 / 170124542557) := by
    rw [show ((170124542557 / 125000000000) : ℝ) = ((125000000000 / 170124542557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_377_neg : (142367241 / 1000000000) ≤ -Real.log (1000 / 1153) ∧
    -Real.log (1000 / 1153) ≤ (71183621 / 500000000) := by
  have h := checkLog_sound (w := (153 / 2153)) (n := 12)
    (lo := (142367241 / 1000000000)) (hi := (71183621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153 / 1000) = 1/(1000 / 1153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_377 : Bounds (142367241 / 1000000000) (71183621 / 500000000) (Real.log (1153 / 1000)) := by
  have h := reflection_log_377_neg
  have he : Real.log (1153 / 1000) = -Real.log (1000 / 1153) := by
    rw [show ((1153 / 1000) : ℝ) = ((1000 / 1153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_378_neg : (20756823 / 125000000) ≤ -Real.log (847 / 1000) ∧
    -Real.log (847 / 1000) ≤ (33210917 / 200000000) := by
  have h := checkLog_sound (w := (153 / 1847)) (n := 12)
    (lo := (20756823 / 125000000)) (hi := (33210917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 847) = 1/(847 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_378 : Bounds (-33210917 / 200000000) (-20756823 / 125000000) (Real.log (847 / 1000)) := by
  have h := reflection_log_378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_379_neg : (38247 / 250000000) ≤ -Real.log (1000000 / 1000153) ∧
    -Real.log (1000000 / 1000153) ≤ (152989 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 2000153)) (n := 12)
    (lo := (38247 / 250000000)) (hi := (152989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000153 / 1000000) = 1/(1000000 / 1000153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_379 : Bounds (38247 / 250000000) (152989 / 1000000000) (Real.log (1000153 / 1000000)) := by
  have h := reflection_log_379_neg
  have he : Real.log (1000153 / 1000000) = -Real.log (1000000 / 1000153) := by
    rw [show ((1000153 / 1000000) : ℝ) = ((1000000 / 1000153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_380_neg : (153011 / 1000000000) ≤ -Real.log (999847 / 1000000) ∧
    -Real.log (999847 / 1000000) ≤ (38253 / 250000000) := by
  have h := checkLog_sound (w := (153 / 1999847)) (n := 12)
    (lo := (153011 / 1000000000)) (hi := (38253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999847) = 1/(999847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_380 : Bounds (-38253 / 250000000) (-153011 / 1000000000) (Real.log (999847 / 1000000)) := by
  have h := reflection_log_380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_381_neg : (1477979 / 20000000) ≤ -Real.log (500000 / 538349) ∧
    -Real.log (500000 / 538349) ≤ (73898951 / 1000000000) := by
  have h := checkLog_sound (w := (38349 / 1038349)) (n := 12)
    (lo := (1477979 / 20000000)) (hi := (73898951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538349 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538349 / 500000) = 1/(500000 / 538349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_381 : Bounds (1477979 / 20000000) (73898951 / 1000000000) (Real.log (538349 / 500000)) := by
  have h := reflection_log_381_neg
  have he : Real.log (538349 / 500000) = -Real.log (500000 / 538349) := by
    rw [show ((538349 / 500000) : ℝ) = ((500000 / 538349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_382_neg : (9974863 / 125000000) ≤ -Real.log (461651 / 500000) ∧
    -Real.log (461651 / 500000) ≤ (15959781 / 200000000) := by
  have h := checkLog_sound (w := (38349 / 961651)) (n := 12)
    (lo := (9974863 / 125000000)) (hi := (15959781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461651) = 1/(461651 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_382 : Bounds (-15959781 / 200000000) (-9974863 / 125000000) (Real.log (461651 / 500000)) := by
  have h := reflection_log_382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_383_neg : (185221 / 2500000) ≤ -Real.log (500000 / 538451) ∧
    -Real.log (500000 / 538451) ≤ (74088401 / 1000000000) := by
  have h := checkLog_sound (w := (38451 / 1038451)) (n := 12)
    (lo := (185221 / 2500000)) (hi := (74088401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538451 / 500000) = 1/(500000 / 538451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_383 : Bounds (185221 / 2500000) (74088401 / 1000000000) (Real.log (538451 / 500000)) := by
  have h := reflection_log_383_neg
  have he : Real.log (538451 / 500000) = -Real.log (500000 / 538451) := by
    rw [show ((538451 / 500000) : ℝ) = ((500000 / 538451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


