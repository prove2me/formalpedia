-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0423Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0423Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:40:47.811868+00:00
-- url     : https://prove2.me/theorems/0f23e6e2-5620-46c3-b259-974b6783934a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0423Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0424Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0423Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0424Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0425Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0426Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0427Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0423Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0424Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0425Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0426Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0427Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0423Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0424Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0425Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0426Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0427Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0423Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0424Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0425Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0426Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0427Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0423Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0423
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (3893917 / 20000000) ≤ -Real.log (10240 / 12441) ∧
    -Real.log (10240 / 12441) ≤ (194695851 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 22681)) (n := 12)
    (lo := (3893917 / 20000000)) (hi := (194695851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12441 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12441 / 10240) = 1/(10240 / 12441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (3893917 / 20000000) (194695851 / 1000000000) (Real.log (12441 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12441 / 10240) = -Real.log (10240 / 12441) := by
    rw [show ((12441 / 10240) : ℝ) = ((10240 / 12441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (120998461 / 500000000) ≤ -Real.log (8039 / 10240) ∧
    -Real.log (8039 / 10240) ≤ (241996923 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 18279)) (n := 12)
    (lo := (120998461 / 500000000)) (hi := (241996923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8039) = 1/(8039 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-241996923 / 1000000000) (-120998461 / 500000000) (Real.log (8039 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (194454683 / 1000000000) ≤ -Real.log (5120 / 6219) ∧
    -Real.log (5120 / 6219) ≤ (48613671 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 11339)) (n := 12)
    (lo := (194454683 / 1000000000)) (hi := (48613671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6219 / 5120) = 1/(5120 / 6219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (194454683 / 1000000000) (48613671 / 250000000) (Real.log (6219 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6219 / 5120) = -Real.log (5120 / 6219) := by
    rw [show ((6219 / 5120) : ℝ) = ((5120 / 6219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241623811 / 1000000000) ≤ -Real.log (4021 / 5120) ∧
    -Real.log (4021 / 5120) ≤ (60405953 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 9141)) (n := 12)
    (lo := (241623811 / 1000000000)) (hi := (60405953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4021) = 1/(4021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60405953 / 250000000) (-241623811 / 1000000000) (Real.log (4021 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (357592491 / 1000000000) ≤ -Real.log (5120 / 7321) ∧
    -Real.log (5120 / 7321) ≤ (89398123 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 12441)) (n := 12)
    (lo := (357592491 / 1000000000)) (hi := (89398123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7321 / 5120) = 1/(5120 / 7321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (357592491 / 1000000000) (89398123 / 250000000) (Real.log (7321 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7321 / 5120) = -Real.log (5120 / 7321) := by
    rw [show ((7321 / 5120) : ℝ) = ((5120 / 7321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (561913347 / 1000000000) ≤ -Real.log (2919 / 5120) ∧
    -Real.log (2919 / 5120) ≤ (140478337 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 8039)) (n := 12)
    (lo := (561913347 / 1000000000)) (hi := (140478337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2919) = 1/(2919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-140478337 / 250000000) (-561913347 / 1000000000) (Real.log (2919 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (357182627 / 1000000000) ≤ -Real.log (2560 / 3659) ∧
    -Real.log (2560 / 3659) ≤ (89295657 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 6219)) (n := 12)
    (lo := (357182627 / 1000000000)) (hi := (89295657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3659 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3659 / 2560) = 1/(2560 / 3659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (357182627 / 1000000000) (89295657 / 250000000) (Real.log (3659 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3659 / 2560) = -Real.log (2560 / 3659) := by
    rw [show ((3659 / 2560) : ℝ) = ((2560 / 3659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4487089 / 8000000) ≤ -Real.log (1461 / 2560) ∧
    -Real.log (1461 / 2560) ≤ (280443063 / 500000000) := by
  have h := checkLog_sound (w := (1099 / 4021)) (n := 12)
    (lo := (4487089 / 8000000)) (hi := (280443063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1461) = 1/(1461 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-280443063 / 500000000) (-4487089 / 8000000) (Real.log (1461 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66758911 / 250000000) ≤ -Real.log (1000000 / 1306087) ∧
    -Real.log (1000000 / 1306087) ≤ (53407129 / 200000000) := by
  have h := checkLog_sound (w := (306087 / 2306087)) (n := 12)
    (lo := (66758911 / 250000000)) (hi := (53407129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306087 / 1000000) = 1/(1000000 / 1306087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66758911 / 250000000) (53407129 / 200000000) (Real.log (1306087 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1306087 / 1000000) = -Real.log (1000000 / 1306087) := by
    rw [show ((1306087 / 1000000) : ℝ) = ((1000000 / 1306087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182704343 / 500000000) ≤ -Real.log (693913 / 1000000) ∧
    -Real.log (693913 / 1000000) ≤ (365408687 / 1000000000) := by
  have h := checkLog_sound (w := (306087 / 1693913)) (n := 12)
    (lo := (182704343 / 500000000)) (hi := (365408687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693913) = 1/(693913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-365408687 / 1000000000) (-182704343 / 500000000) (Real.log (693913 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66840439 / 250000000) ≤ -Real.log (1000000 / 1306513) ∧
    -Real.log (1000000 / 1306513) ≤ (267361757 / 1000000000) := by
  have h := checkLog_sound (w := (306513 / 2306513)) (n := 12)
    (lo := (66840439 / 250000000)) (hi := (267361757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306513 / 1000000) = 1/(1000000 / 1306513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66840439 / 250000000) (267361757 / 1000000000) (Real.log (1306513 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1306513 / 1000000) = -Real.log (1000000 / 1306513) := by
    rw [show ((1306513 / 1000000) : ℝ) = ((1000000 / 1306513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2859553 / 7812500) ≤ -Real.log (693487 / 1000000) ∧
    -Real.log (693487 / 1000000) ≤ (73204557 / 200000000) := by
  have h := checkLog_sound (w := (306513 / 1693487)) (n := 12)
    (lo := (2859553 / 7812500)) (hi := (73204557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693487) = 1/(693487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-73204557 / 200000000) (-2859553 / 7812500) (Real.log (693487 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (200652513 / 1000000000) ≤ -Real.log (5000 / 6111) ∧
    -Real.log (5000 / 6111) ≤ (100326257 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 11111)) (n := 12)
    (lo := (200652513 / 1000000000)) (hi := (100326257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6111 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6111 / 5000) = 1/(5000 / 6111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (200652513 / 1000000000) (100326257 / 500000000) (Real.log (6111 / 5000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (6111 / 5000) = -Real.log (5000 / 6111) := by
    rw [show ((6111 / 5000) : ℝ) = ((5000 / 6111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (251285857 / 1000000000) ≤ -Real.log (3889 / 5000) ∧
    -Real.log (3889 / 5000) ≤ (125642929 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 8889)) (n := 12)
    (lo := (251285857 / 1000000000)) (hi := (125642929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3889) = 1/(3889 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-125642929 / 500000000) (-251285857 / 1000000000) (Real.log (3889 / 5000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20091921 / 100000000) ≤ -Real.log (500000 / 611263) ∧
    -Real.log (500000 / 611263) ≤ (200919211 / 1000000000) := by
  have h := checkLog_sound (w := (111263 / 1111263)) (n := 12)
    (lo := (20091921 / 100000000)) (hi := (200919211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611263 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611263 / 500000) = 1/(500000 / 611263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20091921 / 100000000) (200919211 / 1000000000) (Real.log (611263 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (611263 / 500000) = -Real.log (500000 / 611263) := by
    rw [show ((611263 / 500000) : ℝ) = ((500000 / 611263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (62926269 / 250000000) ≤ -Real.log (388737 / 500000) ∧
    -Real.log (388737 / 500000) ≤ (251705077 / 1000000000) := by
  have h := checkLog_sound (w := (111263 / 888737)) (n := 12)
    (lo := (62926269 / 250000000)) (hi := (251705077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388737) = 1/(388737 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-251705077 / 1000000000) (-62926269 / 250000000) (Real.log (388737 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (63244433 / 100000000) ≤ -Real.log (250000000000 / 470551423593) ∧
    -Real.log (250000000000 / 470551423593) ≤ (632444331 / 1000000000) := by
  have h := checkLog_sound (w := (220551423593 / 720551423593)) (n := 12)
    (lo := (63244433 / 100000000)) (hi := (632444331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470551423593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470551423593 / 250000000000) = 1/(250000000000 / 470551423593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (63244433 / 100000000) (632444331 / 1000000000) (Real.log (470551423593 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (470551423593 / 250000000000) = -Real.log (250000000000 / 470551423593) := by
    rw [show ((470551423593 / 250000000000) : ℝ) = ((250000000000 / 470551423593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (633384541 / 1000000000) ≤ -Real.log (500000000000 / 941988097831) ∧
    -Real.log (500000000000 / 941988097831) ≤ (316692271 / 500000000) := by
  have h := checkLog_sound (w := (441988097831 / 1441988097831)) (n := 12)
    (lo := (633384541 / 1000000000)) (hi := (316692271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941988097831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941988097831 / 500000000000) = 1/(500000000000 / 941988097831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (633384541 / 1000000000) (316692271 / 500000000) (Real.log (941988097831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (941988097831 / 500000000000) = -Real.log (500000000000 / 941988097831) := by
    rw [show ((941988097831 / 500000000000) : ℝ) = ((500000000000 / 941988097831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (45193837 / 100000000) ≤ -Real.log (500000000000 / 785677552069) ∧
    -Real.log (500000000000 / 785677552069) ≤ (451938371 / 1000000000) := by
  have h := checkLog_sound (w := (285677552069 / 1285677552069)) (n := 12)
    (lo := (45193837 / 100000000)) (hi := (451938371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785677552069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785677552069 / 500000000000) = 1/(500000000000 / 785677552069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (45193837 / 100000000) (451938371 / 1000000000) (Real.log (785677552069 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (785677552069 / 500000000000) = -Real.log (500000000000 / 785677552069) := by
    rw [show ((785677552069 / 500000000000) : ℝ) = ((500000000000 / 785677552069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (226312143 / 500000000) ≤ -Real.log (500000000000 / 786216645187) ∧
    -Real.log (500000000000 / 786216645187) ≤ (452624287 / 1000000000) := by
  have h := checkLog_sound (w := (286216645187 / 1286216645187)) (n := 12)
    (lo := (226312143 / 500000000)) (hi := (452624287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786216645187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786216645187 / 500000000000) = 1/(500000000000 / 786216645187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (226312143 / 500000000) (452624287 / 1000000000) (Real.log (786216645187 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (786216645187 / 500000000000) = -Real.log (500000000000 / 786216645187) := by
    rw [show ((786216645187 / 500000000000) : ℝ) = ((500000000000 / 786216645187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0423

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0424Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0424
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (194454683 / 1000000000) ≤ -Real.log (5120 / 6219) ∧
    -Real.log (5120 / 6219) ≤ (48613671 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 11339)) (n := 12)
    (lo := (194454683 / 1000000000)) (hi := (48613671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6219 / 5120) = 1/(5120 / 6219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (194454683 / 1000000000) (48613671 / 250000000) (Real.log (6219 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6219 / 5120) = -Real.log (5120 / 6219) := by
    rw [show ((6219 / 5120) : ℝ) = ((5120 / 6219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241623811 / 1000000000) ≤ -Real.log (4021 / 5120) ∧
    -Real.log (4021 / 5120) ≤ (60405953 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 9141)) (n := 12)
    (lo := (241623811 / 1000000000)) (hi := (60405953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4021) = 1/(4021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60405953 / 250000000) (-241623811 / 1000000000) (Real.log (4021 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (194213457 / 1000000000) ≤ -Real.log (2048 / 2487) ∧
    -Real.log (2048 / 2487) ≤ (97106729 / 500000000) := by
  have h := checkLog_sound (w := (439 / 4535)) (n := 12)
    (lo := (194213457 / 1000000000)) (hi := (97106729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2487 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2487 / 2048) = 1/(2048 / 2487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (194213457 / 1000000000) (97106729 / 500000000) (Real.log (2487 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2487 / 2048) = -Real.log (2048 / 2487) := by
    rw [show ((2487 / 2048) : ℝ) = ((2048 / 2487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241250839 / 1000000000) ≤ -Real.log (1609 / 2048) ∧
    -Real.log (1609 / 2048) ≤ (6031271 / 25000000) := by
  have h := checkLog_sound (w := (439 / 3657)) (n := 12)
    (lo := (241250839 / 1000000000)) (hi := (6031271 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1609) = 1/(1609 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6031271 / 25000000) (-241250839 / 1000000000) (Real.log (1609 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (357182627 / 1000000000) ≤ -Real.log (2560 / 3659) ∧
    -Real.log (2560 / 3659) ≤ (89295657 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 6219)) (n := 12)
    (lo := (357182627 / 1000000000)) (hi := (89295657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3659 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3659 / 2560) = 1/(2560 / 3659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (357182627 / 1000000000) (89295657 / 250000000) (Real.log (3659 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3659 / 2560) = -Real.log (2560 / 3659) := by
    rw [show ((3659 / 2560) : ℝ) = ((2560 / 3659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (4487089 / 8000000) ≤ -Real.log (1461 / 2560) ∧
    -Real.log (1461 / 2560) ≤ (280443063 / 500000000) := by
  have h := checkLog_sound (w := (1099 / 4021)) (n := 12)
    (lo := (4487089 / 8000000)) (hi := (280443063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1461) = 1/(1461 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-280443063 / 500000000) (-4487089 / 8000000) (Real.log (1461 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71354519 / 200000000) ≤ -Real.log (1024 / 1463) ∧
    -Real.log (1024 / 1463) ≤ (89193149 / 250000000) := by
  have h := checkLog_sound (w := (439 / 2487)) (n := 12)
    (lo := (71354519 / 200000000)) (hi := (89193149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1024) = 1/(1024 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71354519 / 200000000) (89193149 / 250000000) (Real.log (1463 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1463 / 1024) = -Real.log (1024 / 1463) := by
    rw [show ((1463 / 1024) : ℝ) = ((1024 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (279929979 / 500000000) ≤ -Real.log (585 / 1024) ∧
    -Real.log (585 / 1024) ≤ (559859959 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1609)) (n := 12)
    (lo := (279929979 / 500000000)) (hi := (559859959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 585) = 1/(585 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-559859959 / 1000000000) (-279929979 / 500000000) (Real.log (585 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (266710191 / 1000000000) ≤ -Real.log (500000 / 652831) ∧
    -Real.log (500000 / 652831) ≤ (16669387 / 62500000) := by
  have h := checkLog_sound (w := (152831 / 1152831)) (n := 12)
    (lo := (266710191 / 1000000000)) (hi := (16669387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652831 / 500000) = 1/(500000 / 652831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (266710191 / 1000000000) (16669387 / 62500000) (Real.log (652831 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (652831 / 500000) = -Real.log (500000 / 652831) := by
    rw [show ((652831 / 500000) : ℝ) = ((500000 / 652831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72959281 / 200000000) ≤ -Real.log (347169 / 500000) ∧
    -Real.log (347169 / 500000) ≤ (182398203 / 500000000) := by
  have h := checkLog_sound (w := (152831 / 847169)) (n := 12)
    (lo := (72959281 / 200000000)) (hi := (182398203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 347169) = 1/(347169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-182398203 / 500000000) (-72959281 / 200000000) (Real.log (347169 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (267036409 / 1000000000) ≤ -Real.log (125000 / 163261) ∧
    -Real.log (125000 / 163261) ≤ (26703641 / 100000000) := by
  have h := checkLog_sound (w := (38261 / 288261)) (n := 12)
    (lo := (267036409 / 1000000000)) (hi := (26703641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163261 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163261 / 125000) = 1/(125000 / 163261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (267036409 / 1000000000) (26703641 / 100000000) (Real.log (163261 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (163261 / 125000) = -Real.log (125000 / 163261) := by
    rw [show ((163261 / 125000) : ℝ) = ((125000 / 163261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (365410127 / 1000000000) ≤ -Real.log (86739 / 125000) ∧
    -Real.log (86739 / 125000) ≤ (22838133 / 62500000) := by
  have h := checkLog_sound (w := (38261 / 211739)) (n := 12)
    (lo := (365410127 / 1000000000)) (hi := (22838133 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 86739) = 1/(86739 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22838133 / 62500000) (-365410127 / 1000000000) (Real.log (86739 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (50096641 / 250000000) ≤ -Real.log (320 / 391) ∧
    -Real.log (320 / 391) ≤ (40077313 / 200000000) := by
  have h := checkLog_sound (w := (71 / 711)) (n := 12)
    (lo := (50096641 / 250000000)) (hi := (40077313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391 / 320) = 1/(320 / 391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (50096641 / 250000000) (40077313 / 200000000) (Real.log (391 / 320)) := by
  have h := reflection_log_13_neg
  have he : Real.log (391 / 320) = -Real.log (320 / 391) := by
    rw [show ((391 / 320) : ℝ) = ((320 / 391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (250868099 / 1000000000) ≤ -Real.log (249 / 320) ∧
    -Real.log (249 / 320) ≤ (2508681 / 10000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 249) = 1/(249 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2508681 / 10000000) (-250868099 / 1000000000) (Real.log (249 / 320)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (200653331 / 1000000000) ≤ -Real.log (1000000 / 1222201) ∧
    -Real.log (1000000 / 1222201) ≤ (50163333 / 250000000) := by
  have h := checkLog_sound (w := (222201 / 2222201)) (n := 12)
    (lo := (200653331 / 1000000000)) (hi := (50163333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222201 / 1000000) = 1/(1000000 / 1222201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (200653331 / 1000000000) (50163333 / 250000000) (Real.log (1222201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1222201 / 1000000) = -Real.log (1000000 / 1222201) := by
    rw [show ((1222201 / 1000000) : ℝ) = ((1000000 / 1222201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (125643571 / 500000000) ≤ -Real.log (777799 / 1000000) ∧
    -Real.log (777799 / 1000000) ≤ (251287143 / 1000000000) := by
  have h := checkLog_sound (w := (222201 / 1777799)) (n := 12)
    (lo := (125643571 / 500000000)) (hi := (251287143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777799) = 1/(777799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-251287143 / 1000000000) (-125643571 / 500000000) (Real.log (777799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (631506597 / 1000000000) ≤ -Real.log (500000000000 / 940220757037) ∧
    -Real.log (500000000000 / 940220757037) ≤ (315753299 / 500000000) := by
  have h := checkLog_sound (w := (440220757037 / 1440220757037)) (n := 12)
    (lo := (631506597 / 1000000000)) (hi := (315753299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940220757037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940220757037 / 500000000000) = 1/(500000000000 / 940220757037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (631506597 / 1000000000) (315753299 / 500000000) (Real.log (940220757037 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (940220757037 / 500000000000) = -Real.log (500000000000 / 940220757037) := by
    rw [show ((940220757037 / 500000000000) : ℝ) = ((500000000000 / 940220757037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (632446537 / 1000000000) ≤ -Real.log (7812500000 / 14704764437) ∧
    -Real.log (7812500000 / 14704764437) ≤ (316223269 / 500000000) := by
  have h := checkLog_sound (w := (6892264437 / 22517264437)) (n := 12)
    (lo := (632446537 / 1000000000)) (hi := (316223269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14704764437 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14704764437 / 7812500000) = 1/(7812500000 / 14704764437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (632446537 / 1000000000) (316223269 / 500000000) (Real.log (14704764437 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14704764437 / 7812500000) = -Real.log (7812500000 / 14704764437) := by
    rw [show ((14704764437 / 7812500000) : ℝ) = ((7812500000 / 14704764437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (451254663 / 1000000000) ≤ -Real.log (62500000000 / 98142570281) ∧
    -Real.log (62500000000 / 98142570281) ≤ (56406833 / 125000000) := by
  have h := checkLog_sound (w := (35642570281 / 160642570281)) (n := 12)
    (lo := (451254663 / 1000000000)) (hi := (56406833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98142570281 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98142570281 / 62500000000) = 1/(62500000000 / 98142570281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (451254663 / 1000000000) (56406833 / 125000000) (Real.log (98142570281 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (98142570281 / 62500000000) = -Real.log (62500000000 / 98142570281) := by
    rw [show ((98142570281 / 62500000000) : ℝ) = ((62500000000 / 98142570281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (225970237 / 500000000) ≤ -Real.log (500000000000 / 785679205039) ∧
    -Real.log (500000000000 / 785679205039) ≤ (18077619 / 40000000) := by
  have h := checkLog_sound (w := (285679205039 / 1285679205039)) (n := 12)
    (lo := (225970237 / 500000000)) (hi := (18077619 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785679205039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785679205039 / 500000000000) = 1/(500000000000 / 785679205039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (225970237 / 500000000) (18077619 / 40000000) (Real.log (785679205039 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (785679205039 / 500000000000) = -Real.log (500000000000 / 785679205039) := by
    rw [show ((785679205039 / 500000000000) : ℝ) = ((500000000000 / 785679205039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0424

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0425Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0425
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (194213457 / 1000000000) ≤ -Real.log (2048 / 2487) ∧
    -Real.log (2048 / 2487) ≤ (97106729 / 500000000) := by
  have h := checkLog_sound (w := (439 / 4535)) (n := 12)
    (lo := (194213457 / 1000000000)) (hi := (97106729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2487 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2487 / 2048) = 1/(2048 / 2487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (194213457 / 1000000000) (97106729 / 500000000) (Real.log (2487 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2487 / 2048) = -Real.log (2048 / 2487) := by
    rw [show ((2487 / 2048) : ℝ) = ((2048 / 2487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241250839 / 1000000000) ≤ -Real.log (1609 / 2048) ∧
    -Real.log (1609 / 2048) ≤ (6031271 / 25000000) := by
  have h := checkLog_sound (w := (439 / 3657)) (n := 12)
    (lo := (241250839 / 1000000000)) (hi := (6031271 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1609) = 1/(1609 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6031271 / 25000000) (-241250839 / 1000000000) (Real.log (1609 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (96986087 / 500000000) ≤ -Real.log (640 / 777) ∧
    -Real.log (640 / 777) ≤ (7758887 / 40000000) := by
  have h := checkLog_sound (w := (137 / 1417)) (n := 12)
    (lo := (96986087 / 500000000)) (hi := (7758887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777 / 640) = 1/(640 / 777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (96986087 / 500000000) (7758887 / 40000000) (Real.log (777 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (777 / 640) = -Real.log (640 / 777) := by
    rw [show ((777 / 640) : ℝ) = ((640 / 777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (120439003 / 500000000) ≤ -Real.log (503 / 640) ∧
    -Real.log (503 / 640) ≤ (240878007 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 1143)) (n := 12)
    (lo := (120439003 / 500000000)) (hi := (240878007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 503) = 1/(503 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240878007 / 1000000000) (-120439003 / 500000000) (Real.log (503 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71354519 / 200000000) ≤ -Real.log (1024 / 1463) ∧
    -Real.log (1024 / 1463) ≤ (89193149 / 250000000) := by
  have h := checkLog_sound (w := (439 / 2487)) (n := 12)
    (lo := (71354519 / 200000000)) (hi := (89193149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1024) = 1/(1024 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (71354519 / 200000000) (89193149 / 250000000) (Real.log (1463 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1463 / 1024) = -Real.log (1024 / 1463) := by
    rw [show ((1463 / 1024) : ℝ) = ((1024 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279929979 / 500000000) ≤ -Real.log (585 / 1024) ∧
    -Real.log (585 / 1024) ≤ (559859959 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1609)) (n := 12)
    (lo := (279929979 / 500000000)) (hi := (559859959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 585) = 1/(585 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-559859959 / 1000000000) (-279929979 / 500000000) (Real.log (585 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71272479 / 200000000) ≤ -Real.log (320 / 457) ∧
    -Real.log (320 / 457) ≤ (89090599 / 250000000) := by
  have h := checkLog_sound (w := (137 / 777)) (n := 12)
    (lo := (71272479 / 200000000)) (hi := (89090599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457 / 320) = 1/(320 / 457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71272479 / 200000000) (89090599 / 250000000) (Real.log (457 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (457 / 320) = -Real.log (320 / 457) := by
    rw [show ((457 / 320) : ℝ) = ((320 / 457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (279417421 / 500000000) ≤ -Real.log (183 / 320) ∧
    -Real.log (183 / 320) ≤ (558834843 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 183) = 1/(183 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-558834843 / 1000000000) (-279417421 / 500000000) (Real.log (183 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (266384633 / 1000000000) ≤ -Real.log (1000000 / 1305237) ∧
    -Real.log (1000000 / 1305237) ≤ (133192317 / 500000000) := by
  have h := checkLog_sound (w := (305237 / 2305237)) (n := 12)
    (lo := (266384633 / 1000000000)) (hi := (133192317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305237 / 1000000) = 1/(1000000 / 1305237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (266384633 / 1000000000) (133192317 / 500000000) (Real.log (1305237 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1305237 / 1000000) = -Real.log (1000000 / 1305237) := by
    rw [show ((1305237 / 1000000) : ℝ) = ((1000000 / 1305237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182092249 / 500000000) ≤ -Real.log (694763 / 1000000) ∧
    -Real.log (694763 / 1000000) ≤ (364184499 / 1000000000) := by
  have h := checkLog_sound (w := (305237 / 1694763)) (n := 12)
    (lo := (182092249 / 500000000)) (hi := (364184499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 694763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 694763) = 1/(694763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-364184499 / 1000000000) (-182092249 / 500000000) (Real.log (694763 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266710957 / 1000000000) ≤ -Real.log (1000000 / 1305663) ∧
    -Real.log (1000000 / 1305663) ≤ (133355479 / 500000000) := by
  have h := checkLog_sound (w := (305663 / 2305663)) (n := 12)
    (lo := (266710957 / 1000000000)) (hi := (133355479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305663 / 1000000) = 1/(1000000 / 1305663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266710957 / 1000000000) (133355479 / 500000000) (Real.log (1305663 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1305663 / 1000000) = -Real.log (1000000 / 1305663) := by
    rw [show ((1305663 / 1000000) : ℝ) = ((1000000 / 1305663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (72959569 / 200000000) ≤ -Real.log (694337 / 1000000) ∧
    -Real.log (694337 / 1000000) ≤ (182398923 / 500000000) := by
  have h := checkLog_sound (w := (305663 / 1694337)) (n := 12)
    (lo := (72959569 / 200000000)) (hi := (182398923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 694337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 694337) = 1/(694337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-182398923 / 500000000) (-72959569 / 200000000) (Real.log (694337 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6253767 / 31250000) ≤ -Real.log (20000 / 24431) ∧
    -Real.log (20000 / 24431) ≤ (40024109 / 200000000) := by
  have h := checkLog_sound (w := (4431 / 44431)) (n := 12)
    (lo := (6253767 / 31250000)) (hi := (40024109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24431 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24431 / 20000) = 1/(20000 / 24431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6253767 / 31250000) (40024109 / 200000000) (Real.log (24431 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24431 / 20000) = -Real.log (20000 / 24431) := by
    rw [show ((24431 / 20000) : ℝ) = ((20000 / 24431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (50090103 / 200000000) ≤ -Real.log (15569 / 20000) ∧
    -Real.log (15569 / 20000) ≤ (62612629 / 250000000) := by
  have h := checkLog_sound (w := (4431 / 35569)) (n := 12)
    (lo := (50090103 / 200000000)) (hi := (62612629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15569) = 1/(15569 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62612629 / 250000000) (-50090103 / 200000000) (Real.log (15569 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100193691 / 500000000) ≤ -Real.log (250000 / 305469) ∧
    -Real.log (250000 / 305469) ≤ (200387383 / 1000000000) := by
  have h := checkLog_sound (w := (55469 / 555469)) (n := 12)
    (lo := (100193691 / 500000000)) (hi := (200387383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305469 / 250000) = 1/(250000 / 305469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100193691 / 500000000) (200387383 / 1000000000) (Real.log (305469 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (305469 / 250000) = -Real.log (250000 / 305469) := by
    rw [show ((305469 / 250000) : ℝ) = ((250000 / 305469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31358673 / 125000000) ≤ -Real.log (194531 / 250000) ∧
    -Real.log (194531 / 250000) ≤ (50173877 / 200000000) := by
  have h := checkLog_sound (w := (55469 / 444531)) (n := 12)
    (lo := (31358673 / 125000000)) (hi := (50173877 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194531) = 1/(194531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-50173877 / 200000000) (-31358673 / 125000000) (Real.log (194531 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (157642283 / 250000000) ≤ -Real.log (500000000000 / 939339746071) ∧
    -Real.log (500000000000 / 939339746071) ≤ (630569133 / 1000000000) := by
  have h := checkLog_sound (w := (439339746071 / 1439339746071)) (n := 12)
    (lo := (157642283 / 250000000)) (hi := (630569133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939339746071 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939339746071 / 500000000000) = 1/(500000000000 / 939339746071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (157642283 / 250000000) (630569133 / 1000000000) (Real.log (939339746071 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (939339746071 / 500000000000) = -Real.log (500000000000 / 939339746071) := by
    rw [show ((939339746071 / 500000000000) : ℝ) = ((500000000000 / 939339746071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (631508803 / 1000000000) ≤ -Real.log (500000000000 / 940222831277) ∧
    -Real.log (500000000000 / 940222831277) ≤ (157877201 / 250000000) := by
  have h := checkLog_sound (w := (440222831277 / 1440222831277)) (n := 12)
    (lo := (631508803 / 1000000000)) (hi := (157877201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940222831277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940222831277 / 500000000000) = 1/(500000000000 / 940222831277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (631508803 / 1000000000) (157877201 / 250000000) (Real.log (940222831277 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (940222831277 / 500000000000) = -Real.log (500000000000 / 940222831277) := by
    rw [show ((940222831277 / 500000000000) : ℝ) = ((500000000000 / 940222831277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22528553 / 50000000) ≤ -Real.log (50000000000 / 78460402081) ∧
    -Real.log (50000000000 / 78460402081) ≤ (450571061 / 1000000000) := by
  have h := checkLog_sound (w := (28460402081 / 128460402081)) (n := 12)
    (lo := (22528553 / 50000000)) (hi := (450571061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78460402081 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78460402081 / 50000000000) = 1/(50000000000 / 78460402081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (22528553 / 50000000) (450571061 / 1000000000) (Real.log (78460402081 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (78460402081 / 50000000000) = -Real.log (50000000000 / 78460402081) := by
    rw [show ((78460402081 / 50000000000) : ℝ) = ((50000000000 / 78460402081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (451256767 / 1000000000) ≤ -Real.log (250000000000 / 392571106919) ∧
    -Real.log (250000000000 / 392571106919) ≤ (7050887 / 15625000) := by
  have h := checkLog_sound (w := (142571106919 / 642571106919)) (n := 12)
    (lo := (451256767 / 1000000000)) (hi := (7050887 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392571106919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392571106919 / 250000000000) = 1/(250000000000 / 392571106919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (451256767 / 1000000000) (7050887 / 15625000) (Real.log (392571106919 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (392571106919 / 250000000000) = -Real.log (250000000000 / 392571106919) := by
    rw [show ((392571106919 / 250000000000) : ℝ) = ((250000000000 / 392571106919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0425

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0426Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0426
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (96986087 / 500000000) ≤ -Real.log (640 / 777) ∧
    -Real.log (640 / 777) ≤ (7758887 / 40000000) := by
  have h := checkLog_sound (w := (137 / 1417)) (n := 12)
    (lo := (96986087 / 500000000)) (hi := (7758887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777 / 640) = 1/(640 / 777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (96986087 / 500000000) (7758887 / 40000000) (Real.log (777 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (777 / 640) = -Real.log (640 / 777) := by
    rw [show ((777 / 640) : ℝ) = ((640 / 777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (120439003 / 500000000) ≤ -Real.log (503 / 640) ∧
    -Real.log (503 / 640) ≤ (240878007 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 1143)) (n := 12)
    (lo := (120439003 / 500000000)) (hi := (240878007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 503) = 1/(503 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240878007 / 1000000000) (-120439003 / 500000000) (Real.log (503 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12108177 / 62500000) ≤ -Real.log (10240 / 12429) ∧
    -Real.log (10240 / 12429) ≤ (193730833 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 22669)) (n := 12)
    (lo := (12108177 / 62500000)) (hi := (193730833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12429 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12429 / 10240) = 1/(10240 / 12429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12108177 / 62500000) (193730833 / 1000000000) (Real.log (12429 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12429 / 10240) = -Real.log (10240 / 12429) := by
    rw [show ((12429 / 10240) : ℝ) = ((10240 / 12429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7515791 / 31250000) ≤ -Real.log (8051 / 10240) ∧
    -Real.log (8051 / 10240) ≤ (240505313 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 18291)) (n := 12)
    (lo := (7515791 / 31250000)) (hi := (240505313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8051) = 1/(8051 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240505313 / 1000000000) (-7515791 / 31250000) (Real.log (8051 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71272479 / 200000000) ≤ -Real.log (320 / 457) ∧
    -Real.log (320 / 457) ≤ (89090599 / 250000000) := by
  have h := checkLog_sound (w := (137 / 777)) (n := 12)
    (lo := (71272479 / 200000000)) (hi := (89090599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457 / 320) = 1/(320 / 457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (71272479 / 200000000) (89090599 / 250000000) (Real.log (457 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (457 / 320) = -Real.log (320 / 457) := by
    rw [show ((457 / 320) : ℝ) = ((320 / 457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279417421 / 500000000) ≤ -Real.log (183 / 320) ∧
    -Real.log (183 / 320) ≤ (558834843 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 183) = 1/(183 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-558834843 / 1000000000) (-279417421 / 500000000) (Real.log (183 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (177976013 / 500000000) ≤ -Real.log (5120 / 7309) ∧
    -Real.log (5120 / 7309) ≤ (355952027 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 12429)) (n := 12)
    (lo := (177976013 / 500000000)) (hi := (355952027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7309 / 5120) = 1/(5120 / 7309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (177976013 / 500000000) (355952027 / 1000000000) (Real.log (7309 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7309 / 5120) = -Real.log (5120 / 7309) := by
    rw [show ((7309 / 5120) : ℝ) = ((5120 / 7309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (557810777 / 1000000000) ≤ -Real.log (2931 / 5120) ∧
    -Real.log (2931 / 5120) ≤ (278905389 / 500000000) := by
  have h := checkLog_sound (w := (2189 / 8051)) (n := 12)
    (lo := (557810777 / 1000000000)) (hi := (278905389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2931) = 1/(2931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-278905389 / 500000000) (-557810777 / 1000000000) (Real.log (2931 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (133029101 / 500000000) ≤ -Real.log (1000000 / 1304811) ∧
    -Real.log (1000000 / 1304811) ≤ (266058203 / 1000000000) := by
  have h := checkLog_sound (w := (304811 / 2304811)) (n := 12)
    (lo := (133029101 / 500000000)) (hi := (266058203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304811 / 1000000) = 1/(1000000 / 1304811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (133029101 / 500000000) (266058203 / 1000000000) (Real.log (1304811 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1304811 / 1000000) = -Real.log (1000000 / 1304811) := by
    rw [show ((1304811 / 1000000) : ℝ) = ((1000000 / 1304811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (363571527 / 1000000000) ≤ -Real.log (695189 / 1000000) ∧
    -Real.log (695189 / 1000000) ≤ (45446441 / 125000000) := by
  have h := checkLog_sound (w := (304811 / 1695189)) (n := 12)
    (lo := (363571527 / 1000000000)) (hi := (45446441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695189) = 1/(695189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45446441 / 125000000) (-363571527 / 1000000000) (Real.log (695189 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266385399 / 1000000000) ≤ -Real.log (500000 / 652619) ∧
    -Real.log (500000 / 652619) ≤ (1331927 / 5000000) := by
  have h := checkLog_sound (w := (152619 / 1152619)) (n := 12)
    (lo := (266385399 / 1000000000)) (hi := (1331927 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652619 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652619 / 500000) = 1/(500000 / 652619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266385399 / 1000000000) (1331927 / 5000000) (Real.log (652619 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (652619 / 500000) = -Real.log (500000 / 652619) := by
    rw [show ((652619 / 500000) : ℝ) = ((500000 / 652619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (182092969 / 500000000) ≤ -Real.log (347381 / 500000) ∧
    -Real.log (347381 / 500000) ≤ (364185939 / 1000000000) := by
  have h := checkLog_sound (w := (152619 / 847381)) (n := 12)
    (lo := (182092969 / 500000000)) (hi := (364185939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 347381) = 1/(347381 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-364185939 / 1000000000) (-182092969 / 500000000) (Real.log (347381 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (199854453 / 1000000000) ≤ -Real.log (40000 / 48849) ∧
    -Real.log (40000 / 48849) ≤ (99927227 / 500000000) := by
  have h := checkLog_sound (w := (8849 / 88849)) (n := 12)
    (lo := (199854453 / 1000000000)) (hi := (99927227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48849 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48849 / 40000) = 1/(40000 / 48849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (199854453 / 1000000000) (99927227 / 500000000) (Real.log (48849 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (48849 / 40000) = -Real.log (40000 / 48849) := by
    rw [show ((48849 / 40000) : ℝ) = ((40000 / 48849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (125016553 / 500000000) ≤ -Real.log (31151 / 40000) ∧
    -Real.log (31151 / 40000) ≤ (250033107 / 1000000000) := by
  have h := checkLog_sound (w := (8849 / 71151)) (n := 12)
    (lo := (125016553 / 500000000)) (hi := (250033107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31151) = 1/(31151 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-250033107 / 1000000000) (-125016553 / 500000000) (Real.log (31151 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100060681 / 500000000) ≤ -Real.log (1000000 / 1221551) ∧
    -Real.log (1000000 / 1221551) ≤ (200121363 / 1000000000) := by
  have h := checkLog_sound (w := (221551 / 2221551)) (n := 12)
    (lo := (100060681 / 500000000)) (hi := (200121363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221551 / 1000000) = 1/(1000000 / 1221551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100060681 / 500000000) (200121363 / 1000000000) (Real.log (1221551 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1221551 / 1000000) = -Real.log (1000000 / 1221551) := by
    rw [show ((1221551 / 1000000) : ℝ) = ((1000000 / 1221551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1252259 / 5000000) ≤ -Real.log (778449 / 1000000) ∧
    -Real.log (778449 / 1000000) ≤ (250451801 / 1000000000) := by
  have h := checkLog_sound (w := (221551 / 1778449)) (n := 12)
    (lo := (1252259 / 5000000)) (hi := (250451801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778449) = 1/(778449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-250451801 / 1000000000) (-1252259 / 5000000) (Real.log (778449 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (62962973 / 100000000) ≤ -Real.log (250000000000 / 469228871573) ∧
    -Real.log (250000000000 / 469228871573) ≤ (629629731 / 1000000000) := by
  have h := checkLog_sound (w := (219228871573 / 719228871573)) (n := 12)
    (lo := (62962973 / 100000000)) (hi := (629629731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469228871573 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469228871573 / 250000000000) = 1/(250000000000 / 469228871573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (62962973 / 100000000) (629629731 / 1000000000) (Real.log (469228871573 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (469228871573 / 250000000000) = -Real.log (250000000000 / 469228871573) := by
    rw [show ((469228871573 / 250000000000) : ℝ) = ((250000000000 / 469228871573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (630571337 / 1000000000) ≤ -Real.log (250000000000 / 469670908887) ∧
    -Real.log (250000000000 / 469670908887) ≤ (315285669 / 500000000) := by
  have h := checkLog_sound (w := (219670908887 / 719670908887)) (n := 12)
    (lo := (630571337 / 1000000000)) (hi := (315285669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469670908887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469670908887 / 250000000000) = 1/(250000000000 / 469670908887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (630571337 / 1000000000) (315285669 / 500000000) (Real.log (469670908887 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (469670908887 / 250000000000) = -Real.log (250000000000 / 469670908887) := by
    rw [show ((469670908887 / 250000000000) : ℝ) = ((250000000000 / 469670908887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11247189 / 25000000) ≤ -Real.log (500000000000 / 784067927193) ∧
    -Real.log (500000000000 / 784067927193) ≤ (449887561 / 1000000000) := by
  have h := checkLog_sound (w := (284067927193 / 1284067927193)) (n := 12)
    (lo := (11247189 / 25000000)) (hi := (449887561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784067927193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784067927193 / 500000000000) = 1/(500000000000 / 784067927193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (11247189 / 25000000) (449887561 / 1000000000) (Real.log (784067927193 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (784067927193 / 500000000000) = -Real.log (500000000000 / 784067927193) := by
    rw [show ((784067927193 / 500000000000) : ℝ) = ((500000000000 / 784067927193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (450573163 / 1000000000) ≤ -Real.log (500000000000 / 784605671021) ∧
    -Real.log (500000000000 / 784605671021) ≤ (112643291 / 250000000) := by
  have h := checkLog_sound (w := (284605671021 / 1284605671021)) (n := 12)
    (lo := (450573163 / 1000000000)) (hi := (112643291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784605671021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784605671021 / 500000000000) = 1/(500000000000 / 784605671021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (450573163 / 1000000000) (112643291 / 250000000) (Real.log (784605671021 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (784605671021 / 500000000000) = -Real.log (500000000000 / 784605671021) := by
    rw [show ((784605671021 / 500000000000) : ℝ) = ((500000000000 / 784605671021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0426

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0427Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0427
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (12108177 / 62500000) ≤ -Real.log (10240 / 12429) ∧
    -Real.log (10240 / 12429) ≤ (193730833 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 22669)) (n := 12)
    (lo := (12108177 / 62500000)) (hi := (193730833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12429 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12429 / 10240) = 1/(10240 / 12429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12108177 / 62500000) (193730833 / 1000000000) (Real.log (12429 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12429 / 10240) = -Real.log (10240 / 12429) := by
    rw [show ((12429 / 10240) : ℝ) = ((10240 / 12429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7515791 / 31250000) ≤ -Real.log (8051 / 10240) ∧
    -Real.log (8051 / 10240) ≤ (240505313 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 18291)) (n := 12)
    (lo := (7515791 / 31250000)) (hi := (240505313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8051) = 1/(8051 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240505313 / 1000000000) (-7515791 / 31250000) (Real.log (8051 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24186179 / 125000000) ≤ -Real.log (5120 / 6213) ∧
    -Real.log (5120 / 6213) ≤ (193489433 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 11333)) (n := 12)
    (lo := (24186179 / 125000000)) (hi := (193489433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6213 / 5120) = 1/(5120 / 6213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24186179 / 125000000) (193489433 / 1000000000) (Real.log (6213 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6213 / 5120) = -Real.log (5120 / 6213) := by
    rw [show ((6213 / 5120) : ℝ) = ((5120 / 6213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (240132757 / 1000000000) ≤ -Real.log (4027 / 5120) ∧
    -Real.log (4027 / 5120) ≤ (120066379 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 9147)) (n := 12)
    (lo := (240132757 / 1000000000)) (hi := (120066379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4027) = 1/(4027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-120066379 / 500000000) (-240132757 / 1000000000) (Real.log (4027 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177976013 / 500000000) ≤ -Real.log (5120 / 7309) ∧
    -Real.log (5120 / 7309) ≤ (355952027 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 12429)) (n := 12)
    (lo := (177976013 / 500000000)) (hi := (355952027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7309 / 5120) = 1/(5120 / 7309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177976013 / 500000000) (355952027 / 1000000000) (Real.log (7309 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7309 / 5120) = -Real.log (5120 / 7309) := by
    rw [show ((7309 / 5120) : ℝ) = ((5120 / 7309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (557810777 / 1000000000) ≤ -Real.log (2931 / 5120) ∧
    -Real.log (2931 / 5120) ≤ (278905389 / 500000000) := by
  have h := checkLog_sound (w := (2189 / 8051)) (n := 12)
    (lo := (557810777 / 1000000000)) (hi := (278905389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2931) = 1/(2931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-278905389 / 500000000) (-557810777 / 1000000000) (Real.log (2931 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (355541489 / 1000000000) ≤ -Real.log (2560 / 3653) ∧
    -Real.log (2560 / 3653) ≤ (35554149 / 100000000) := by
  have h := checkLog_sound (w := (1093 / 6213)) (n := 12)
    (lo := (355541489 / 1000000000)) (hi := (35554149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3653 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3653 / 2560) = 1/(2560 / 3653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (355541489 / 1000000000) (35554149 / 100000000) (Real.log (3653 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3653 / 2560) = -Real.log (2560 / 3653) := by
    rw [show ((3653 / 2560) : ℝ) = ((2560 / 3653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (556787759 / 1000000000) ≤ -Real.log (1467 / 2560) ∧
    -Real.log (1467 / 2560) ≤ (6959847 / 12500000) := by
  have h := checkLog_sound (w := (1093 / 4027)) (n := 12)
    (lo := (556787759 / 1000000000)) (hi := (6959847 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1467) = 1/(1467 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6959847 / 12500000) (-556787759 / 1000000000) (Real.log (1467 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (265732431 / 1000000000) ≤ -Real.log (500000 / 652193) ∧
    -Real.log (500000 / 652193) ≤ (16608277 / 62500000) := by
  have h := checkLog_sound (w := (152193 / 1152193)) (n := 12)
    (lo := (265732431 / 1000000000)) (hi := (16608277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652193 / 500000) = 1/(500000 / 652193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (265732431 / 1000000000) (16608277 / 62500000) (Real.log (652193 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (652193 / 500000) = -Real.log (500000 / 652193) := by
    rw [show ((652193 / 500000) : ℝ) = ((500000 / 652193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (36296037 / 100000000) ≤ -Real.log (347807 / 500000) ∧
    -Real.log (347807 / 500000) ≤ (362960371 / 1000000000) := by
  have h := checkLog_sound (w := (152193 / 847807)) (n := 12)
    (lo := (36296037 / 100000000)) (hi := (362960371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 347807) = 1/(347807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-362960371 / 1000000000) (-36296037 / 100000000) (Real.log (347807 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266058969 / 1000000000) ≤ -Real.log (250000 / 326203) ∧
    -Real.log (250000 / 326203) ≤ (26605897 / 100000000) := by
  have h := checkLog_sound (w := (76203 / 576203)) (n := 12)
    (lo := (266058969 / 1000000000)) (hi := (26605897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326203 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326203 / 250000) = 1/(250000 / 326203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266058969 / 1000000000) (26605897 / 100000000) (Real.log (326203 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (326203 / 250000) = -Real.log (250000 / 326203) := by
    rw [show ((326203 / 250000) : ℝ) = ((250000 / 326203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (181786483 / 500000000) ≤ -Real.log (173797 / 250000) ∧
    -Real.log (173797 / 250000) ≤ (363572967 / 1000000000) := by
  have h := checkLog_sound (w := (76203 / 423797)) (n := 12)
    (lo := (181786483 / 500000000)) (hi := (363572967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 173797) = 1/(173797 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-363572967 / 1000000000) (-181786483 / 500000000) (Real.log (173797 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (199588291 / 1000000000) ≤ -Real.log (10000 / 12209) ∧
    -Real.log (10000 / 12209) ≤ (49897073 / 250000000) := by
  have h := checkLog_sound (w := (2209 / 22209)) (n := 12)
    (lo := (199588291 / 1000000000)) (hi := (49897073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12209 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12209 / 10000) = 1/(10000 / 12209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (199588291 / 1000000000) (49897073 / 250000000) (Real.log (12209 / 10000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (12209 / 10000) = -Real.log (10000 / 12209) := by
    rw [show ((12209 / 10000) : ℝ) = ((10000 / 12209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (249615871 / 1000000000) ≤ -Real.log (7791 / 10000) ∧
    -Real.log (7791 / 10000) ≤ (487531 / 1953125) := by
  have h := checkLog_sound (w := (2209 / 17791)) (n := 12)
    (lo := (249615871 / 1000000000)) (hi := (487531 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7791) = 1/(7791 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-487531 / 1953125) (-249615871 / 1000000000) (Real.log (7791 / 10000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24981909 / 125000000) ≤ -Real.log (500000 / 610613) ∧
    -Real.log (500000 / 610613) ≤ (199855273 / 1000000000) := by
  have h := checkLog_sound (w := (110613 / 1110613)) (n := 12)
    (lo := (24981909 / 125000000)) (hi := (199855273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610613 / 500000) = 1/(500000 / 610613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24981909 / 125000000) (199855273 / 1000000000) (Real.log (610613 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (610613 / 500000) = -Real.log (500000 / 610613) := by
    rw [show ((610613 / 500000) : ℝ) = ((500000 / 610613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25003439 / 100000000) ≤ -Real.log (389387 / 500000) ∧
    -Real.log (389387 / 500000) ≤ (250034391 / 1000000000) := by
  have h := checkLog_sound (w := (110613 / 889387)) (n := 12)
    (lo := (25003439 / 100000000)) (hi := (250034391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 389387) = 1/(389387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-250034391 / 1000000000) (-25003439 / 100000000) (Real.log (389387 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (314346401 / 500000000) ≤ -Real.log (500000000000 / 937578887141) ∧
    -Real.log (500000000000 / 937578887141) ≤ (628692803 / 1000000000) := by
  have h := checkLog_sound (w := (437578887141 / 1437578887141)) (n := 12)
    (lo := (314346401 / 500000000)) (hi := (628692803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((937578887141 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(937578887141 / 500000000000) = 1/(500000000000 / 937578887141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (314346401 / 500000000) (628692803 / 1000000000) (Real.log (937578887141 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (937578887141 / 500000000000) = -Real.log (500000000000 / 937578887141) := by
    rw [show ((937578887141 / 500000000000) : ℝ) = ((500000000000 / 937578887141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (125926387 / 200000000) ≤ -Real.log (50000000000 / 93845981231) ∧
    -Real.log (50000000000 / 93845981231) ≤ (9837999 / 15625000) := by
  have h := checkLog_sound (w := (43845981231 / 143845981231)) (n := 12)
    (lo := (125926387 / 200000000)) (hi := (9837999 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93845981231 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93845981231 / 50000000000) = 1/(50000000000 / 93845981231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (125926387 / 200000000) (9837999 / 15625000) (Real.log (93845981231 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (93845981231 / 50000000000) = -Real.log (50000000000 / 93845981231) := by
    rw [show ((93845981231 / 50000000000) : ℝ) = ((50000000000 / 93845981231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (449204163 / 1000000000) ≤ -Real.log (125000000000 / 195883070209) ∧
    -Real.log (125000000000 / 195883070209) ≤ (112301041 / 250000000) := by
  have h := checkLog_sound (w := (70883070209 / 320883070209)) (n := 12)
    (lo := (449204163 / 1000000000)) (hi := (112301041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195883070209 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195883070209 / 125000000000) = 1/(125000000000 / 195883070209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (449204163 / 1000000000) (112301041 / 250000000) (Real.log (195883070209 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (195883070209 / 125000000000) = -Real.log (125000000000 / 195883070209) := by
    rw [show ((195883070209 / 125000000000) : ℝ) = ((125000000000 / 195883070209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (224944831 / 500000000) ≤ -Real.log (250000000000 / 392034788013) ∧
    -Real.log (250000000000 / 392034788013) ≤ (449889663 / 1000000000) := by
  have h := checkLog_sound (w := (142034788013 / 642034788013)) (n := 12)
    (lo := (224944831 / 500000000)) (hi := (449889663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392034788013 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392034788013 / 250000000000) = 1/(250000000000 / 392034788013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (224944831 / 500000000) (449889663 / 1000000000) (Real.log (392034788013 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (392034788013 / 250000000000) = -Real.log (250000000000 / 392034788013) := by
    rw [show ((392034788013 / 250000000000) : ℝ) = ((250000000000 / 392034788013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0427

end


