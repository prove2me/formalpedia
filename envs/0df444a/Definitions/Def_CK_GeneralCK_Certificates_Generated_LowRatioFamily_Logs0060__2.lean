-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0060__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0060__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:08:22.478461+00:00
-- url     : https://prove2.me/theorems/deddc630-5be2-4b4a-963e-32c5cdf73717
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0060 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0061)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0060 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0061)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0060 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0061)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0060 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0061) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0060 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0061).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0060 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3840_neg : (93455001 / 1000000000) ≤ -Real.log (910779 / 1000000) ∧
    -Real.log (910779 / 1000000) ≤ (46727501 / 500000000) := by
  have h := checkLog_sound (w := (89221 / 1910779)) (n := 12)
    (lo := (93455001 / 1000000000)) (hi := (46727501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910779) = 1/(910779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3840 : Bounds (-46727501 / 500000000) (-93455001 / 1000000000) (Real.log (910779 / 1000000)) := by
  have h := reflection_log_3840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3841_neg : (85672981 / 1000000000) ≤ -Real.log (20000 / 21789) ∧
    -Real.log (20000 / 21789) ≤ (42836491 / 500000000) := by
  have h := checkLog_sound (w := (1789 / 41789)) (n := 12)
    (lo := (85672981 / 1000000000)) (hi := (42836491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21789 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21789 / 20000) = 1/(20000 / 21789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3841 : Bounds (85672981 / 1000000000) (42836491 / 500000000) (Real.log (21789 / 20000)) := by
  have h := reflection_log_3841_neg
  have he : Real.log (21789 / 20000) = -Real.log (20000 / 21789) := by
    rw [show ((21789 / 20000) : ℝ) = ((20000 / 21789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3842_neg : (46853233 / 500000000) ≤ -Real.log (18211 / 20000) ∧
    -Real.log (18211 / 20000) ≤ (93706467 / 1000000000) := by
  have h := checkLog_sound (w := (1789 / 38211)) (n := 12)
    (lo := (46853233 / 500000000)) (hi := (93706467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18211) = 1/(18211 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3842 : Bounds (-93706467 / 1000000000) (-46853233 / 500000000) (Real.log (18211 / 20000)) := by
  have h := reflection_log_3842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3843_neg : (2008371 / 250000000) ≤ -Real.log (396799479 / 400000000) ∧
    -Real.log (396799479 / 400000000) ≤ (1606697 / 200000000) := by
  have h := checkLog_sound (w := (3200521 / 796799479)) (n := 12)
    (lo := (2008371 / 250000000)) (hi := (1606697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396799479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396799479) = 1/(396799479 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3843 : Bounds (-1606697 / 200000000) (-2008371 / 250000000) (Real.log (396799479 / 400000000)) := by
  have h := reflection_log_3843_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3844_neg : (7992239 / 1000000000) ≤ -Real.log (992039613159 / 1000000000000) ∧
    -Real.log (992039613159 / 1000000000000) ≤ (99903 / 12500000) := by
  have h := checkLog_sound (w := (7960386841 / 1992039613159)) (n := 12)
    (lo := (7992239 / 1000000000)) (hi := (99903 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992039613159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992039613159) = 1/(992039613159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3844 : Bounds (-99903 / 12500000) (-7992239 / 1000000000) (Real.log (992039613159 / 1000000000000)) := by
  have h := reflection_log_3844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3845_neg : (178917763 / 1000000000) ≤ -Real.log (100000000000 / 119592239171) ∧
    -Real.log (100000000000 / 119592239171) ≤ (44729441 / 250000000) := by
  have h := checkLog_sound (w := (19592239171 / 219592239171)) (n := 12)
    (lo := (178917763 / 1000000000)) (hi := (44729441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119592239171 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119592239171 / 100000000000) = 1/(100000000000 / 119592239171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3845 : Bounds (178917763 / 1000000000) (44729441 / 250000000) (Real.log (119592239171 / 100000000000)) := by
  have h := reflection_log_3845_neg
  have he : Real.log (119592239171 / 100000000000) = -Real.log (100000000000 / 119592239171) := by
    rw [show ((119592239171 / 100000000000) : ℝ) = ((100000000000 / 119592239171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3846_neg : (22422431 / 125000000) ≤ -Real.log (500000000000 / 598237329087) ∧
    -Real.log (500000000000 / 598237329087) ≤ (179379449 / 1000000000) := by
  have h := checkLog_sound (w := (98237329087 / 1098237329087)) (n := 12)
    (lo := (22422431 / 125000000)) (hi := (179379449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598237329087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598237329087 / 500000000000) = 1/(500000000000 / 598237329087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3846 : Bounds (22422431 / 125000000) (179379449 / 1000000000) (Real.log (598237329087 / 500000000000)) := by
  have h := reflection_log_3846_neg
  have he : Real.log (598237329087 / 500000000000) = -Real.log (500000000000 / 598237329087) := by
    rw [show ((598237329087 / 500000000000) : ℝ) = ((500000000000 / 598237329087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3847_neg : (359006853 / 1000000000) ≤ -Real.log (1953125000 / 2796692607) ∧
    -Real.log (1953125000 / 2796692607) ≤ (179503427 / 500000000) := by
  have h := checkLog_sound (w := (843567607 / 4749817607)) (n := 12)
    (lo := (359006853 / 1000000000)) (hi := (179503427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2796692607 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2796692607 / 1953125000) = 1/(1953125000 / 2796692607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3847 : Bounds (359006853 / 1000000000) (179503427 / 500000000) (Real.log (2796692607 / 1953125000)) := by
  have h := reflection_log_3847_neg
  have he : Real.log (2796692607 / 1953125000) = -Real.log (1953125000 / 2796692607) := by
    rw [show ((2796692607 / 1953125000) : ℝ) = ((1953125000 / 2796692607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3848_neg : (35921337 / 100000000) ≤ -Real.log (500000000000 / 716101179619) ∧
    -Real.log (500000000000 / 716101179619) ≤ (359213371 / 1000000000) := by
  have h := checkLog_sound (w := (216101179619 / 1216101179619)) (n := 12)
    (lo := (35921337 / 100000000)) (hi := (359213371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716101179619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716101179619 / 500000000000) = 1/(500000000000 / 716101179619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3848 : Bounds (35921337 / 100000000) (359213371 / 1000000000) (Real.log (716101179619 / 500000000000)) := by
  have h := reflection_log_3848_neg
  have he : Real.log (716101179619 / 500000000000) = -Real.log (500000000000 / 716101179619) := by
    rw [show ((716101179619 / 500000000000) : ℝ) = ((500000000000 / 716101179619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3849_neg : (163648291 / 1000000000) ≤ -Real.log (5000 / 5889) ∧
    -Real.log (5000 / 5889) ≤ (40912073 / 250000000) := by
  have h := checkLog_sound (w := (889 / 10889)) (n := 12)
    (lo := (163648291 / 1000000000)) (hi := (40912073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5889 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5889 / 5000) = 1/(5000 / 5889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3849 : Bounds (163648291 / 1000000000) (40912073 / 250000000) (Real.log (5889 / 5000)) := by
  have h := reflection_log_3849_neg
  have he : Real.log (5889 / 5000) = -Real.log (5000 / 5889) := by
    rw [show ((5889 / 5000) : ℝ) = ((5000 / 5889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3850_neg : (48942901 / 250000000) ≤ -Real.log (4111 / 5000) ∧
    -Real.log (4111 / 5000) ≤ (39154321 / 200000000) := by
  have h := checkLog_sound (w := (889 / 9111)) (n := 12)
    (lo := (48942901 / 250000000)) (hi := (39154321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4111) = 1/(4111 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3850 : Bounds (-39154321 / 200000000) (-48942901 / 250000000) (Real.log (4111 / 5000)) := by
  have h := reflection_log_3850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3851_neg : (22223 / 125000000) ≤ -Real.log (5000000 / 5000889) ∧
    -Real.log (5000000 / 5000889) ≤ (35557 / 200000000) := by
  have h := checkLog_sound (w := (889 / 10000889)) (n := 12)
    (lo := (22223 / 125000000)) (hi := (35557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000889 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000889 / 5000000) = 1/(5000000 / 5000889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3851 : Bounds (22223 / 125000000) (35557 / 200000000) (Real.log (5000889 / 5000000)) := by
  have h := reflection_log_3851_neg
  have he : Real.log (5000889 / 5000000) = -Real.log (5000000 / 5000889) := by
    rw [show ((5000889 / 5000000) : ℝ) = ((5000000 / 5000889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3852_neg : (35563 / 200000000) ≤ -Real.log (4999111 / 5000000) ∧
    -Real.log (4999111 / 5000000) ≤ (22227 / 125000000) := by
  have h := checkLog_sound (w := (889 / 9999111)) (n := 12)
    (lo := (35563 / 200000000)) (hi := (22227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999111) = 1/(4999111 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3852 : Bounds (-22227 / 125000000) (-35563 / 200000000) (Real.log (4999111 / 5000000)) := by
  have h := reflection_log_3852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3853_neg : (85509583 / 1000000000) ≤ -Real.log (125000 / 136159) ∧
    -Real.log (125000 / 136159) ≤ (5344349 / 62500000) := by
  have h := checkLog_sound (w := (11159 / 261159)) (n := 12)
    (lo := (85509583 / 1000000000)) (hi := (5344349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136159 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136159 / 125000) = 1/(125000 / 136159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3853 : Bounds (85509583 / 1000000000) (5344349 / 62500000) (Real.log (136159 / 125000)) := by
  have h := reflection_log_3853_neg
  have he : Real.log (136159 / 125000) = -Real.log (125000 / 136159) := by
    rw [show ((136159 / 125000) : ℝ) = ((125000 / 136159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3854_neg : (93510999 / 1000000000) ≤ -Real.log (113841 / 125000) ∧
    -Real.log (113841 / 125000) ≤ (93511 / 1000000) := by
  have h := checkLog_sound (w := (11159 / 238841)) (n := 12)
    (lo := (93510999 / 1000000000)) (hi := (93511 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113841) = 1/(113841 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3854 : Bounds (-93511 / 1000000) (-93510999 / 1000000000) (Real.log (113841 / 125000)) := by
  have h := reflection_log_3854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3855_neg : (685751 / 8000000) ≤ -Real.log (2000 / 2179) ∧
    -Real.log (2000 / 2179) ≤ (21429719 / 250000000) := by
  have h := checkLog_sound (w := (179 / 4179)) (n := 12)
    (lo := (685751 / 8000000)) (hi := (21429719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2179 / 2000) = 1/(2000 / 2179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3855 : Bounds (685751 / 8000000) (21429719 / 250000000) (Real.log (2179 / 2000)) := by
  have h := reflection_log_3855_neg
  have he : Real.log (2179 / 2000) = -Real.log (2000 / 2179) := by
    rw [show ((2179 / 2000) : ℝ) = ((2000 / 2179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3856_neg : (93761379 / 1000000000) ≤ -Real.log (1821 / 2000) ∧
    -Real.log (1821 / 2000) ≤ (4688069 / 50000000) := by
  have h := checkLog_sound (w := (179 / 3821)) (n := 12)
    (lo := (93761379 / 1000000000)) (hi := (4688069 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1821) = 1/(1821 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3856 : Bounds (-4688069 / 50000000) (-93761379 / 1000000000) (Real.log (1821 / 2000)) := by
  have h := reflection_log_3856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3857_neg : (1005313 / 125000000) ≤ -Real.log (3967959 / 4000000) ∧
    -Real.log (3967959 / 4000000) ≤ (1608501 / 200000000) := by
  have h := checkLog_sound (w := (32041 / 7967959)) (n := 12)
    (lo := (1005313 / 125000000)) (hi := (1608501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000000 / 3967959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000000 / 3967959) = 1/(3967959 / 4000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3857 : Bounds (-1608501 / 200000000) (-1005313 / 125000000) (Real.log (3967959 / 4000000)) := by
  have h := reflection_log_3857_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3858_neg : (1000177 / 125000000) ≤ -Real.log (15500476719 / 15625000000) ∧
    -Real.log (15500476719 / 15625000000) ≤ (8001417 / 1000000000) := by
  have h := checkLog_sound (w := (124523281 / 31125476719)) (n := 12)
    (lo := (1000177 / 125000000)) (hi := (8001417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15500476719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15500476719) = 1/(15500476719 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3858 : Bounds (-8001417 / 1000000000) (-1000177 / 125000000) (Real.log (15500476719 / 15625000000)) := by
  have h := reflection_log_3858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3859_neg : (89510291 / 500000000) ≤ -Real.log (125000000000 / 149505670189) ∧
    -Real.log (125000000000 / 149505670189) ≤ (179020583 / 1000000000) := by
  have h := checkLog_sound (w := (24505670189 / 274505670189)) (n := 12)
    (lo := (89510291 / 500000000)) (hi := (179020583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149505670189 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149505670189 / 125000000000) = 1/(125000000000 / 149505670189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3859 : Bounds (89510291 / 500000000) (179020583 / 1000000000) (Real.log (149505670189 / 125000000000)) := by
  have h := reflection_log_3859_neg
  have he : Real.log (149505670189 / 125000000000) = -Real.log (125000000000 / 149505670189) := by
    rw [show ((149505670189 / 125000000000) : ℝ) = ((125000000000 / 149505670189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3860_neg : (35896051 / 200000000) ≤ -Real.log (500000000000 / 598297638661) ∧
    -Real.log (500000000000 / 598297638661) ≤ (2804379 / 15625000) := by
  have h := checkLog_sound (w := (98297638661 / 1098297638661)) (n := 12)
    (lo := (35896051 / 200000000)) (hi := (2804379 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598297638661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598297638661 / 500000000000) = 1/(500000000000 / 598297638661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3860 : Bounds (35896051 / 200000000) (2804379 / 15625000) (Real.log (598297638661 / 500000000000)) := by
  have h := reflection_log_3860_neg
  have he : Real.log (598297638661 / 500000000000) = -Real.log (500000000000 / 598297638661) := by
    rw [show ((598297638661 / 500000000000) : ℝ) = ((500000000000 / 598297638661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3861_neg : (35921337 / 100000000) ≤ -Real.log (250000000000 / 358050589809) ∧
    -Real.log (250000000000 / 358050589809) ≤ (359213371 / 1000000000) := by
  have h := checkLog_sound (w := (108050589809 / 608050589809)) (n := 12)
    (lo := (35921337 / 100000000)) (hi := (359213371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358050589809 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358050589809 / 250000000000) = 1/(250000000000 / 358050589809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3861 : Bounds (35921337 / 100000000) (359213371 / 1000000000) (Real.log (358050589809 / 250000000000)) := by
  have h := reflection_log_3861_neg
  have he : Real.log (358050589809 / 250000000000) = -Real.log (250000000000 / 358050589809) := by
    rw [show ((358050589809 / 250000000000) : ℝ) = ((250000000000 / 358050589809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3862_neg : (44927487 / 125000000) ≤ -Real.log (250000000000 / 358124543907) ∧
    -Real.log (250000000000 / 358124543907) ≤ (359419897 / 1000000000) := by
  have h := checkLog_sound (w := (108124543907 / 608124543907)) (n := 12)
    (lo := (44927487 / 125000000)) (hi := (359419897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358124543907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358124543907 / 250000000000) = 1/(250000000000 / 358124543907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3862 : Bounds (44927487 / 125000000) (359419897 / 1000000000) (Real.log (358124543907 / 250000000000)) := by
  have h := reflection_log_3862_neg
  have he : Real.log (358124543907 / 250000000000) = -Real.log (250000000000 / 358124543907) := by
    rw [show ((358124543907 / 250000000000) : ℝ) = ((250000000000 / 358124543907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3863_neg : (163733191 / 1000000000) ≤ -Real.log (10000 / 11779) ∧
    -Real.log (10000 / 11779) ≤ (20466649 / 125000000) := by
  have h := checkLog_sound (w := (1779 / 21779)) (n := 12)
    (lo := (163733191 / 1000000000)) (hi := (20466649 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11779 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11779 / 10000) = 1/(10000 / 11779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3863 : Bounds (163733191 / 1000000000) (20466649 / 125000000) (Real.log (11779 / 10000)) := by
  have h := reflection_log_3863_neg
  have he : Real.log (11779 / 10000) = -Real.log (10000 / 11779) := by
    rw [show ((11779 / 10000) : ℝ) = ((10000 / 11779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3864_neg : (48973309 / 250000000) ≤ -Real.log (8221 / 10000) ∧
    -Real.log (8221 / 10000) ≤ (195893237 / 1000000000) := by
  have h := checkLog_sound (w := (1779 / 18221)) (n := 12)
    (lo := (48973309 / 250000000)) (hi := (195893237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8221) = 1/(8221 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3864 : Bounds (-195893237 / 1000000000) (-48973309 / 250000000) (Real.log (8221 / 10000)) := by
  have h := reflection_log_3864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3865_neg : (44471 / 250000000) ≤ -Real.log (10000000 / 10001779) ∧
    -Real.log (10000000 / 10001779) ≤ (35577 / 200000000) := by
  have h := checkLog_sound (w := (1779 / 20001779)) (n := 12)
    (lo := (44471 / 250000000)) (hi := (35577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001779 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001779 / 10000000) = 1/(10000000 / 10001779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3865 : Bounds (44471 / 250000000) (35577 / 200000000) (Real.log (10001779 / 10000000)) := by
  have h := reflection_log_3865_neg
  have he : Real.log (10001779 / 10000000) = -Real.log (10000000 / 10001779) := by
    rw [show ((10001779 / 10000000) : ℝ) = ((10000000 / 10001779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3866_neg : (35583 / 200000000) ≤ -Real.log (9998221 / 10000000) ∧
    -Real.log (9998221 / 10000000) ≤ (44479 / 250000000) := by
  have h := checkLog_sound (w := (1779 / 19998221)) (n := 12)
    (lo := (35583 / 200000000)) (hi := (44479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998221) = 1/(9998221 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3866 : Bounds (-44479 / 250000000) (-35583 / 200000000) (Real.log (9998221 / 10000000)) := by
  have h := reflection_log_3866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3867_neg : (42778201 / 500000000) ≤ -Real.log (1000000 / 1089323) ∧
    -Real.log (1000000 / 1089323) ≤ (85556403 / 1000000000) := by
  have h := checkLog_sound (w := (89323 / 2089323)) (n := 12)
    (lo := (42778201 / 500000000)) (hi := (85556403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089323 / 1000000) = 1/(1000000 / 1089323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3867 : Bounds (42778201 / 500000000) (85556403 / 1000000000) (Real.log (1089323 / 1000000)) := by
  have h := reflection_log_3867_neg
  have he : Real.log (1089323 / 1000000) = -Real.log (1000000 / 1089323) := by
    rw [show ((1089323 / 1000000) : ℝ) = ((1000000 / 1089323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3868_neg : (93567 / 1000000) ≤ -Real.log (910677 / 1000000) ∧
    -Real.log (910677 / 1000000) ≤ (93567001 / 1000000000) := by
  have h := checkLog_sound (w := (89323 / 1910677)) (n := 12)
    (lo := (93567 / 1000000)) (hi := (93567001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910677) = 1/(910677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3868 : Bounds (-93567001 / 1000000000) (-93567 / 1000000) (Real.log (910677 / 1000000)) := by
  have h := reflection_log_3868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3869_neg : (21441421 / 250000000) ≤ -Real.log (1000000 / 1089551) ∧
    -Real.log (1000000 / 1089551) ≤ (17153137 / 200000000) := by
  have h := checkLog_sound (w := (89551 / 2089551)) (n := 12)
    (lo := (21441421 / 250000000)) (hi := (17153137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089551 / 1000000) = 1/(1000000 / 1089551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3869 : Bounds (21441421 / 250000000) (17153137 / 200000000) (Real.log (1089551 / 1000000)) := by
  have h := reflection_log_3869_neg
  have he : Real.log (1089551 / 1000000) = -Real.log (1000000 / 1089551) := by
    rw [show ((1089551 / 1000000) : ℝ) = ((1000000 / 1089551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3870_neg : (46908697 / 500000000) ≤ -Real.log (910449 / 1000000) ∧
    -Real.log (910449 / 1000000) ≤ (18763479 / 200000000) := by
  have h := checkLog_sound (w := (89551 / 1910449)) (n := 12)
    (lo := (46908697 / 500000000)) (hi := (18763479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910449) = 1/(910449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3870 : Bounds (-18763479 / 200000000) (-46908697 / 500000000) (Real.log (910449 / 1000000)) := by
  have h := reflection_log_3870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3871_neg : (8051709 / 1000000000) ≤ -Real.log (991980618399 / 1000000000000) ∧
    -Real.log (991980618399 / 1000000000000) ≤ (805171 / 100000000) := by
  have h := checkLog_sound (w := (8019381601 / 1991980618399)) (n := 12)
    (lo := (8051709 / 1000000000)) (hi := (805171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991980618399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991980618399) = 1/(991980618399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3871 : Bounds (-805171 / 100000000) (-8051709 / 1000000000) (Real.log (991980618399 / 1000000000000)) := by
  have h := reflection_log_3871_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3872_neg : (8010597 / 1000000000) ≤ -Real.log (992021401671 / 1000000000000) ∧
    -Real.log (992021401671 / 1000000000000) ≤ (4005299 / 500000000) := by
  have h := checkLog_sound (w := (7978598329 / 1992021401671)) (n := 12)
    (lo := (8010597 / 1000000000)) (hi := (4005299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992021401671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992021401671) = 1/(992021401671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3872 : Bounds (-4005299 / 500000000) (-8010597 / 1000000000) (Real.log (992021401671 / 1000000000000)) := by
  have h := reflection_log_3872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3873_neg : (89561701 / 500000000) ≤ -Real.log (1953125000 / 2336266299) ∧
    -Real.log (1953125000 / 2336266299) ≤ (179123403 / 1000000000) := by
  have h := checkLog_sound (w := (383141299 / 4289391299)) (n := 12)
    (lo := (89561701 / 500000000)) (hi := (179123403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2336266299 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2336266299 / 1953125000) = 1/(1953125000 / 2336266299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3873 : Bounds (89561701 / 500000000) (179123403 / 1000000000) (Real.log (2336266299 / 1953125000)) := by
  have h := reflection_log_3873_neg
  have he : Real.log (2336266299 / 1953125000) = -Real.log (1953125000 / 2336266299) := by
    rw [show ((2336266299 / 1953125000) : ℝ) = ((1953125000 / 2336266299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3874_neg : (179583079 / 1000000000) ≤ -Real.log (400000000 / 478687329) ∧
    -Real.log (400000000 / 478687329) ≤ (4489577 / 25000000) := by
  have h := checkLog_sound (w := (78687329 / 878687329)) (n := 12)
    (lo := (179583079 / 1000000000)) (hi := (4489577 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478687329 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478687329 / 400000000) = 1/(400000000 / 478687329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3874 : Bounds (179583079 / 1000000000) (4489577 / 25000000) (Real.log (478687329 / 400000000)) := by
  have h := reflection_log_3874_neg
  have he : Real.log (478687329 / 400000000) = -Real.log (400000000 / 478687329) := by
    rw [show ((478687329 / 400000000) : ℝ) = ((400000000 / 478687329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3875_neg : (44927487 / 125000000) ≤ -Real.log (500000000000 / 716249087813) ∧
    -Real.log (500000000000 / 716249087813) ≤ (359419897 / 1000000000) := by
  have h := checkLog_sound (w := (216249087813 / 1216249087813)) (n := 12)
    (lo := (44927487 / 125000000)) (hi := (359419897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716249087813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716249087813 / 500000000000) = 1/(500000000000 / 716249087813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3875 : Bounds (44927487 / 125000000) (359419897 / 1000000000) (Real.log (716249087813 / 500000000000)) := by
  have h := reflection_log_3875_neg
  have he : Real.log (716249087813 / 500000000000) = -Real.log (500000000000 / 716249087813) := by
    rw [show ((716249087813 / 500000000000) : ℝ) = ((500000000000 / 716249087813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3876_neg : (89906607 / 250000000) ≤ -Real.log (62500000000 / 89549628999) ∧
    -Real.log (62500000000 / 89549628999) ≤ (359626429 / 1000000000) := by
  have h := checkLog_sound (w := (27049628999 / 152049628999)) (n := 12)
    (lo := (89906607 / 250000000)) (hi := (359626429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89549628999 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89549628999 / 62500000000) = 1/(62500000000 / 89549628999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3876 : Bounds (89906607 / 250000000) (359626429 / 1000000000) (Real.log (89549628999 / 62500000000)) := by
  have h := reflection_log_3876_neg
  have he : Real.log (89549628999 / 62500000000) = -Real.log (62500000000 / 89549628999) := by
    rw [show ((89549628999 / 62500000000) : ℝ) = ((62500000000 / 89549628999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3877_neg : (32763617 / 200000000) ≤ -Real.log (500 / 589) ∧
    -Real.log (500 / 589) ≤ (81909043 / 500000000) := by
  have h := checkLog_sound (w := (89 / 1089)) (n := 12)
    (lo := (32763617 / 200000000)) (hi := (81909043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589 / 500) = 1/(500 / 589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3877 : Bounds (32763617 / 200000000) (81909043 / 500000000) (Real.log (589 / 500)) := by
  have h := reflection_log_3877_neg
  have he : Real.log (589 / 500) = -Real.log (500 / 589) := by
    rw [show ((589 / 500) : ℝ) = ((500 / 589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3878_neg : (196014883 / 1000000000) ≤ -Real.log (411 / 500) ∧
    -Real.log (411 / 500) ≤ (49003721 / 250000000) := by
  have h := checkLog_sound (w := (89 / 911)) (n := 12)
    (lo := (196014883 / 1000000000)) (hi := (49003721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 411) = 1/(411 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3878 : Bounds (-49003721 / 250000000) (-196014883 / 1000000000) (Real.log (411 / 500)) := by
  have h := reflection_log_3878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3879_neg : (2781 / 15625000) ≤ -Real.log (500000 / 500089) ∧
    -Real.log (500000 / 500089) ≤ (35597 / 200000000) := by
  have h := checkLog_sound (w := (89 / 1000089)) (n := 12)
    (lo := (2781 / 15625000)) (hi := (35597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500089 / 500000) = 1/(500000 / 500089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3879 : Bounds (2781 / 15625000) (35597 / 200000000) (Real.log (500089 / 500000)) := by
  have h := reflection_log_3879_neg
  have he : Real.log (500089 / 500000) = -Real.log (500000 / 500089) := by
    rw [show ((500089 / 500000) : ℝ) = ((500000 / 500089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3880_neg : (35603 / 200000000) ≤ -Real.log (499911 / 500000) ∧
    -Real.log (499911 / 500000) ≤ (5563 / 31250000) := by
  have h := checkLog_sound (w := (89 / 999911)) (n := 12)
    (lo := (35603 / 200000000)) (hi := (5563 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499911) = 1/(499911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3880 : Bounds (-5563 / 31250000) (-35603 / 200000000) (Real.log (499911 / 500000)) := by
  have h := reflection_log_3880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3881_neg : (85602301 / 1000000000) ≤ -Real.log (1000000 / 1089373) ∧
    -Real.log (1000000 / 1089373) ≤ (42801151 / 500000000) := by
  have h := checkLog_sound (w := (89373 / 2089373)) (n := 12)
    (lo := (85602301 / 1000000000)) (hi := (42801151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089373 / 1000000) = 1/(1000000 / 1089373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3881 : Bounds (85602301 / 1000000000) (42801151 / 500000000) (Real.log (1089373 / 1000000)) := by
  have h := reflection_log_3881_neg
  have he : Real.log (1089373 / 1000000) = -Real.log (1000000 / 1089373) := by
    rw [show ((1089373 / 1000000) : ℝ) = ((1000000 / 1089373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3882_neg : (18724381 / 200000000) ≤ -Real.log (910627 / 1000000) ∧
    -Real.log (910627 / 1000000) ≤ (46810953 / 500000000) := by
  have h := checkLog_sound (w := (89373 / 1910627)) (n := 12)
    (lo := (18724381 / 200000000)) (hi := (46810953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910627) = 1/(910627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3882 : Bounds (-46810953 / 500000000) (-18724381 / 200000000) (Real.log (910627 / 1000000)) := by
  have h := reflection_log_3882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3883_neg : (85812491 / 1000000000) ≤ -Real.log (500000 / 544801) ∧
    -Real.log (500000 / 544801) ≤ (21453123 / 250000000) := by
  have h := checkLog_sound (w := (44801 / 1044801)) (n := 12)
    (lo := (85812491 / 1000000000)) (hi := (21453123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544801 / 500000) = 1/(500000 / 544801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3883 : Bounds (85812491 / 1000000000) (21453123 / 250000000) (Real.log (544801 / 500000)) := by
  have h := reflection_log_3883_neg
  have he : Real.log (544801 / 500000) = -Real.log (500000 / 544801) := by
    rw [show ((544801 / 500000) : ℝ) = ((500000 / 544801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3884_neg : (23468353 / 250000000) ≤ -Real.log (455199 / 500000) ∧
    -Real.log (455199 / 500000) ≤ (93873413 / 1000000000) := by
  have h := checkLog_sound (w := (44801 / 955199)) (n := 12)
    (lo := (23468353 / 250000000)) (hi := (93873413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455199) = 1/(455199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3884 : Bounds (-93873413 / 1000000000) (-23468353 / 250000000) (Real.log (455199 / 500000)) := by
  have h := reflection_log_3884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3885_neg : (201523 / 25000000) ≤ -Real.log (247992870399 / 250000000000) ∧
    -Real.log (247992870399 / 250000000000) ≤ (8060921 / 1000000000) := by
  have h := checkLog_sound (w := (2007129601 / 497992870399)) (n := 12)
    (lo := (201523 / 25000000)) (hi := (8060921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247992870399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247992870399) = 1/(247992870399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3885 : Bounds (-8060921 / 1000000000) (-201523 / 25000000) (Real.log (247992870399 / 250000000000)) := by
  have h := reflection_log_3885_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3886_neg : (2004901 / 250000000) ≤ -Real.log (992012466871 / 1000000000000) ∧
    -Real.log (992012466871 / 1000000000000) ≤ (1603921 / 200000000) := by
  have h := checkLog_sound (w := (7987533129 / 1992012466871)) (n := 12)
    (lo := (2004901 / 250000000)) (hi := (1603921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992012466871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992012466871) = 1/(992012466871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3886 : Bounds (-1603921 / 200000000) (-2004901 / 250000000) (Real.log (992012466871 / 1000000000000)) := by
  have h := reflection_log_3886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3887_neg : (179224207 / 1000000000) ≤ -Real.log (31250000000 / 37384029081) ∧
    -Real.log (31250000000 / 37384029081) ≤ (11201513 / 62500000) := by
  have h := checkLog_sound (w := (6134029081 / 68634029081)) (n := 12)
    (lo := (179224207 / 1000000000)) (hi := (11201513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37384029081 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37384029081 / 31250000000) = 1/(31250000000 / 37384029081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3887 : Bounds (179224207 / 1000000000) (11201513 / 62500000) (Real.log (37384029081 / 31250000000)) := by
  have h := reflection_log_3887_neg
  have he : Real.log (37384029081 / 31250000000) = -Real.log (31250000000 / 37384029081) := by
    rw [show ((37384029081 / 31250000000) : ℝ) = ((31250000000 / 37384029081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3888_neg : (11230369 / 62500000) ≤ -Real.log (500000000000 / 598420690731) ∧
    -Real.log (500000000000 / 598420690731) ≤ (35937181 / 200000000) := by
  have h := checkLog_sound (w := (98420690731 / 1098420690731)) (n := 12)
    (lo := (11230369 / 62500000)) (hi := (35937181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598420690731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598420690731 / 500000000000) = 1/(500000000000 / 598420690731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3888 : Bounds (11230369 / 62500000) (35937181 / 200000000) (Real.log (598420690731 / 500000000000)) := by
  have h := reflection_log_3888_neg
  have he : Real.log (598420690731 / 500000000000) = -Real.log (500000000000 / 598420690731) := by
    rw [show ((598420690731 / 500000000000) : ℝ) = ((500000000000 / 598420690731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3889_neg : (89906607 / 250000000) ≤ -Real.log (500000000000 / 716397031991) ∧
    -Real.log (500000000000 / 716397031991) ≤ (359626429 / 1000000000) := by
  have h := checkLog_sound (w := (216397031991 / 1216397031991)) (n := 12)
    (lo := (89906607 / 250000000)) (hi := (359626429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716397031991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716397031991 / 500000000000) = 1/(500000000000 / 716397031991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3889 : Bounds (89906607 / 250000000) (359626429 / 1000000000) (Real.log (716397031991 / 500000000000)) := by
  have h := reflection_log_3889_neg
  have he : Real.log (716397031991 / 500000000000) = -Real.log (500000000000 / 716397031991) := by
    rw [show ((716397031991 / 500000000000) : ℝ) = ((500000000000 / 716397031991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3890_neg : (359832969 / 1000000000) ≤ -Real.log (250000000000 / 358272506083) ∧
    -Real.log (250000000000 / 358272506083) ≤ (35983297 / 100000000) := by
  have h := checkLog_sound (w := (108272506083 / 608272506083)) (n := 12)
    (lo := (359832969 / 1000000000)) (hi := (35983297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358272506083 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358272506083 / 250000000000) = 1/(250000000000 / 358272506083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3890 : Bounds (359832969 / 1000000000) (35983297 / 100000000) (Real.log (358272506083 / 250000000000)) := by
  have h := reflection_log_3890_neg
  have he : Real.log (358272506083 / 250000000000) = -Real.log (250000000000 / 358272506083) := by
    rw [show ((358272506083 / 250000000000) : ℝ) = ((250000000000 / 358272506083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3891_neg : (163902971 / 1000000000) ≤ -Real.log (10000 / 11781) ∧
    -Real.log (10000 / 11781) ≤ (40975743 / 250000000) := by
  have h := checkLog_sound (w := (1781 / 21781)) (n := 12)
    (lo := (163902971 / 1000000000)) (hi := (40975743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11781 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11781 / 10000) = 1/(10000 / 11781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3891 : Bounds (163902971 / 1000000000) (40975743 / 250000000) (Real.log (11781 / 10000)) := by
  have h := reflection_log_3891_neg
  have he : Real.log (11781 / 10000) = -Real.log (10000 / 11781) := by
    rw [show ((11781 / 10000) : ℝ) = ((10000 / 11781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3892_neg : (39227309 / 200000000) ≤ -Real.log (8219 / 10000) ∧
    -Real.log (8219 / 10000) ≤ (98068273 / 500000000) := by
  have h := checkLog_sound (w := (1781 / 18219)) (n := 12)
    (lo := (39227309 / 200000000)) (hi := (98068273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8219) = 1/(8219 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3892 : Bounds (-98068273 / 500000000) (-39227309 / 200000000) (Real.log (8219 / 10000)) := by
  have h := reflection_log_3892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3893_neg : (44521 / 250000000) ≤ -Real.log (10000000 / 10001781) ∧
    -Real.log (10000000 / 10001781) ≤ (35617 / 200000000) := by
  have h := checkLog_sound (w := (1781 / 20001781)) (n := 12)
    (lo := (44521 / 250000000)) (hi := (35617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001781 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001781 / 10000000) = 1/(10000000 / 10001781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3893 : Bounds (44521 / 250000000) (35617 / 200000000) (Real.log (10001781 / 10000000)) := by
  have h := reflection_log_3893_neg
  have he : Real.log (10001781 / 10000000) = -Real.log (10000000 / 10001781) := by
    rw [show ((10001781 / 10000000) : ℝ) = ((10000000 / 10001781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3894_neg : (35623 / 200000000) ≤ -Real.log (9998219 / 10000000) ∧
    -Real.log (9998219 / 10000000) ≤ (44529 / 250000000) := by
  have h := checkLog_sound (w := (1781 / 19998219)) (n := 12)
    (lo := (35623 / 200000000)) (hi := (44529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998219) = 1/(9998219 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3894 : Bounds (-44529 / 250000000) (-35623 / 200000000) (Real.log (9998219 / 10000000)) := by
  have h := reflection_log_3894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3895_neg : (21412279 / 250000000) ≤ -Real.log (62500 / 68089) ∧
    -Real.log (62500 / 68089) ≤ (85649117 / 1000000000) := by
  have h := checkLog_sound (w := (5589 / 130589)) (n := 12)
    (lo := (21412279 / 250000000)) (hi := (85649117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68089 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68089 / 62500) = 1/(62500 / 68089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3895 : Bounds (21412279 / 250000000) (85649117 / 1000000000) (Real.log (68089 / 62500)) := by
  have h := reflection_log_3895_neg
  have he : Real.log (68089 / 62500) = -Real.log (62500 / 68089) := by
    rw [show ((68089 / 62500) : ℝ) = ((62500 / 68089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3896_neg : (11709739 / 125000000) ≤ -Real.log (56911 / 62500) ∧
    -Real.log (56911 / 62500) ≤ (93677913 / 1000000000) := by
  have h := checkLog_sound (w := (5589 / 119411)) (n := 12)
    (lo := (11709739 / 125000000)) (hi := (93677913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56911) = 1/(56911 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3896 : Bounds (-93677913 / 1000000000) (-11709739 / 125000000) (Real.log (56911 / 62500)) := by
  have h := reflection_log_3896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3897_neg : (2683103 / 31250000) ≤ -Real.log (1000000 / 1089653) ∧
    -Real.log (1000000 / 1089653) ≤ (85859297 / 1000000000) := by
  have h := checkLog_sound (w := (89653 / 2089653)) (n := 12)
    (lo := (2683103 / 31250000)) (hi := (85859297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089653 / 1000000) = 1/(1000000 / 1089653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3897 : Bounds (2683103 / 31250000) (85859297 / 1000000000) (Real.log (1089653 / 1000000)) := by
  have h := reflection_log_3897_neg
  have he : Real.log (1089653 / 1000000) = -Real.log (1000000 / 1089653) := by
    rw [show ((1089653 / 1000000) : ℝ) = ((1000000 / 1089653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3898_neg : (93929433 / 1000000000) ≤ -Real.log (910347 / 1000000) ∧
    -Real.log (910347 / 1000000) ≤ (46964717 / 500000000) := by
  have h := checkLog_sound (w := (89653 / 1910347)) (n := 12)
    (lo := (93929433 / 1000000000)) (hi := (46964717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910347) = 1/(910347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3898 : Bounds (-46964717 / 500000000) (-93929433 / 1000000000) (Real.log (910347 / 1000000)) := by
  have h := reflection_log_3898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3899_neg : (1008767 / 125000000) ≤ -Real.log (991962339591 / 1000000000000) ∧
    -Real.log (991962339591 / 1000000000000) ≤ (8070137 / 1000000000) := by
  have h := checkLog_sound (w := (8037660409 / 1991962339591)) (n := 12)
    (lo := (1008767 / 125000000)) (hi := (8070137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991962339591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991962339591) = 1/(991962339591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3899 : Bounds (-8070137 / 1000000000) (-1008767 / 125000000) (Real.log (991962339591 / 1000000000000)) := by
  have h := reflection_log_3899_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3900_neg : (2007199 / 250000000) ≤ -Real.log (3875013079 / 3906250000) ∧
    -Real.log (3875013079 / 3906250000) ≤ (8028797 / 1000000000) := by
  have h := checkLog_sound (w := (31236921 / 7781263079)) (n := 12)
    (lo := (2007199 / 250000000)) (hi := (8028797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3875013079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3875013079) = 1/(3875013079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3900 : Bounds (-8028797 / 1000000000) (-2007199 / 250000000) (Real.log (3875013079 / 3906250000)) := by
  have h := reflection_log_3900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3901_neg : (44831757 / 250000000) ≤ -Real.log (250000000000 / 299102985363) ∧
    -Real.log (250000000000 / 299102985363) ≤ (179327029 / 1000000000) := by
  have h := checkLog_sound (w := (49102985363 / 549102985363)) (n := 12)
    (lo := (44831757 / 250000000)) (hi := (179327029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299102985363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299102985363 / 250000000000) = 1/(250000000000 / 299102985363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3901 : Bounds (44831757 / 250000000) (179327029 / 1000000000) (Real.log (299102985363 / 250000000000)) := by
  have h := reflection_log_3901_neg
  have he : Real.log (299102985363 / 250000000000) = -Real.log (250000000000 / 299102985363) := by
    rw [show ((299102985363 / 250000000000) : ℝ) = ((250000000000 / 299102985363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3902_neg : (17978873 / 100000000) ≤ -Real.log (500000000000 / 598482227107) ∧
    -Real.log (500000000000 / 598482227107) ≤ (179788731 / 1000000000) := by
  have h := checkLog_sound (w := (98482227107 / 1098482227107)) (n := 12)
    (lo := (17978873 / 100000000)) (hi := (179788731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598482227107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598482227107 / 500000000000) = 1/(500000000000 / 598482227107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3902 : Bounds (17978873 / 100000000) (179788731 / 1000000000) (Real.log (598482227107 / 500000000000)) := by
  have h := reflection_log_3902_neg
  have he : Real.log (598482227107 / 500000000000) = -Real.log (500000000000 / 598482227107) := by
    rw [show ((598482227107 / 500000000000) : ℝ) = ((500000000000 / 598482227107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3903_neg : (359832969 / 1000000000) ≤ -Real.log (100000000000 / 143309002433) ∧
    -Real.log (100000000000 / 143309002433) ≤ (35983297 / 100000000) := by
  have h := checkLog_sound (w := (43309002433 / 243309002433)) (n := 12)
    (lo := (359832969 / 1000000000)) (hi := (35983297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143309002433 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143309002433 / 100000000000) = 1/(100000000000 / 143309002433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3903 : Bounds (359832969 / 1000000000) (35983297 / 100000000) (Real.log (143309002433 / 100000000000)) := by
  have h := reflection_log_3903_neg
  have he : Real.log (143309002433 / 100000000000) = -Real.log (100000000000 / 143309002433) := by
    rw [show ((143309002433 / 100000000000) : ℝ) = ((100000000000 / 143309002433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0061 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3904_neg : (360039517 / 1000000000) ≤ -Real.log (500000000000 / 716693028349) ∧
    -Real.log (500000000000 / 716693028349) ≤ (180019759 / 500000000) := by
  have h := checkLog_sound (w := (216693028349 / 1216693028349)) (n := 12)
    (lo := (360039517 / 1000000000)) (hi := (180019759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716693028349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716693028349 / 500000000000) = 1/(500000000000 / 716693028349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3904 : Bounds (360039517 / 1000000000) (180019759 / 500000000) (Real.log (716693028349 / 500000000000)) := by
  have h := reflection_log_3904_neg
  have he : Real.log (716693028349 / 500000000000) = -Real.log (500000000000 / 716693028349) := by
    rw [show ((716693028349 / 500000000000) : ℝ) = ((500000000000 / 716693028349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3905_neg : (3279757 / 20000000) ≤ -Real.log (5000 / 5891) ∧
    -Real.log (5000 / 5891) ≤ (163987851 / 1000000000) := by
  have h := checkLog_sound (w := (891 / 10891)) (n := 12)
    (lo := (3279757 / 20000000)) (hi := (163987851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5891 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5891 / 5000) = 1/(5000 / 5891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3905 : Bounds (3279757 / 20000000) (163987851 / 1000000000) (Real.log (5891 / 5000)) := by
  have h := reflection_log_3905_neg
  have he : Real.log (5891 / 5000) = -Real.log (5000 / 5891) := by
    rw [show ((5891 / 5000) : ℝ) = ((5000 / 5891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3906_neg : (98129111 / 500000000) ≤ -Real.log (4109 / 5000) ∧
    -Real.log (4109 / 5000) ≤ (196258223 / 1000000000) := by
  have h := checkLog_sound (w := (891 / 9109)) (n := 12)
    (lo := (98129111 / 500000000)) (hi := (196258223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4109) = 1/(4109 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3906 : Bounds (-196258223 / 1000000000) (-98129111 / 500000000) (Real.log (4109 / 5000)) := by
  have h := reflection_log_3906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3907_neg : (22273 / 125000000) ≤ -Real.log (5000000 / 5000891) ∧
    -Real.log (5000000 / 5000891) ≤ (35637 / 200000000) := by
  have h := checkLog_sound (w := (891 / 10000891)) (n := 12)
    (lo := (22273 / 125000000)) (hi := (35637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000891 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000891 / 5000000) = 1/(5000000 / 5000891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3907 : Bounds (22273 / 125000000) (35637 / 200000000) (Real.log (5000891 / 5000000)) := by
  have h := reflection_log_3907_neg
  have he : Real.log (5000891 / 5000000) = -Real.log (5000000 / 5000891) := by
    rw [show ((5000891 / 5000000) : ℝ) = ((5000000 / 5000891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3908_neg : (35643 / 200000000) ≤ -Real.log (4999109 / 5000000) ∧
    -Real.log (4999109 / 5000000) ≤ (22277 / 125000000) := by
  have h := checkLog_sound (w := (891 / 9999109)) (n := 12)
    (lo := (35643 / 200000000)) (hi := (22277 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999109) = 1/(4999109 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3908 : Bounds (-22277 / 125000000) (-35643 / 200000000) (Real.log (4999109 / 5000000)) := by
  have h := reflection_log_3908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3909_neg : (10711991 / 125000000) ≤ -Real.log (40000 / 43579) ∧
    -Real.log (40000 / 43579) ≤ (85695929 / 1000000000) := by
  have h := checkLog_sound (w := (3579 / 83579)) (n := 12)
    (lo := (10711991 / 125000000)) (hi := (85695929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43579 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43579 / 40000) = 1/(40000 / 43579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3909 : Bounds (10711991 / 125000000) (85695929 / 1000000000) (Real.log (43579 / 40000)) := by
  have h := reflection_log_3909_neg
  have he : Real.log (43579 / 40000) = -Real.log (40000 / 43579) := by
    rw [show ((43579 / 40000) : ℝ) = ((40000 / 43579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3910_neg : (46866961 / 500000000) ≤ -Real.log (36421 / 40000) ∧
    -Real.log (36421 / 40000) ≤ (93733923 / 1000000000) := by
  have h := checkLog_sound (w := (3579 / 76421)) (n := 12)
    (lo := (46866961 / 500000000)) (hi := (93733923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36421) = 1/(36421 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3910 : Bounds (-93733923 / 1000000000) (-46866961 / 500000000) (Real.log (36421 / 40000)) := by
  have h := reflection_log_3910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3911_neg : (85906099 / 1000000000) ≤ -Real.log (125000 / 136213) ∧
    -Real.log (125000 / 136213) ≤ (859061 / 10000000) := by
  have h := checkLog_sound (w := (11213 / 261213)) (n := 12)
    (lo := (85906099 / 1000000000)) (hi := (859061 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136213 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136213 / 125000) = 1/(125000 / 136213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3911 : Bounds (85906099 / 1000000000) (859061 / 10000000) (Real.log (136213 / 125000)) := by
  have h := reflection_log_3911_neg
  have he : Real.log (136213 / 125000) = -Real.log (125000 / 136213) := by
    rw [show ((136213 / 125000) : ℝ) = ((125000 / 136213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3912_neg : (93985457 / 1000000000) ≤ -Real.log (113787 / 125000) ∧
    -Real.log (113787 / 125000) ≤ (46992729 / 500000000) := by
  have h := checkLog_sound (w := (11213 / 238787)) (n := 12)
    (lo := (93985457 / 1000000000)) (hi := (46992729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113787) = 1/(113787 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3912 : Bounds (-46992729 / 500000000) (-93985457 / 1000000000) (Real.log (113787 / 125000)) := by
  have h := reflection_log_3912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3913_neg : (8079357 / 1000000000) ≤ -Real.log (15499268631 / 15625000000) ∧
    -Real.log (15499268631 / 15625000000) ≤ (4039679 / 500000000) := by
  have h := checkLog_sound (w := (125731369 / 31124268631)) (n := 12)
    (lo := (8079357 / 1000000000)) (hi := (4039679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15499268631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15499268631) = 1/(15499268631 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3913 : Bounds (-4039679 / 500000000) (-8079357 / 1000000000) (Real.log (15499268631 / 15625000000)) := by
  have h := reflection_log_3913_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3914_neg : (8037993 / 1000000000) ≤ -Real.log (1587190759 / 1600000000) ∧
    -Real.log (1587190759 / 1600000000) ≤ (4018997 / 500000000) := by
  have h := checkLog_sound (w := (12809241 / 3187190759)) (n := 12)
    (lo := (8037993 / 1000000000)) (hi := (4018997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1587190759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1587190759) = 1/(1587190759 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3914 : Bounds (-4018997 / 500000000) (-8037993 / 1000000000) (Real.log (1587190759 / 1600000000)) := by
  have h := reflection_log_3914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3915_neg : (179429851 / 1000000000) ≤ -Real.log (100000000000 / 119653496609) ∧
    -Real.log (100000000000 / 119653496609) ≤ (44857463 / 250000000) := by
  have h := checkLog_sound (w := (19653496609 / 219653496609)) (n := 12)
    (lo := (179429851 / 1000000000)) (hi := (44857463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119653496609 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119653496609 / 100000000000) = 1/(100000000000 / 119653496609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3915 : Bounds (179429851 / 1000000000) (44857463 / 250000000) (Real.log (119653496609 / 100000000000)) := by
  have h := reflection_log_3915_neg
  have he : Real.log (119653496609 / 100000000000) = -Real.log (100000000000 / 119653496609) := by
    rw [show ((119653496609 / 100000000000) : ℝ) = ((100000000000 / 119653496609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3916_neg : (179891557 / 1000000000) ≤ -Real.log (250000000000 / 299271885189) ∧
    -Real.log (250000000000 / 299271885189) ≤ (89945779 / 500000000) := by
  have h := checkLog_sound (w := (49271885189 / 549271885189)) (n := 12)
    (lo := (179891557 / 1000000000)) (hi := (89945779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299271885189 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299271885189 / 250000000000) = 1/(250000000000 / 299271885189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3916 : Bounds (179891557 / 1000000000) (89945779 / 500000000) (Real.log (299271885189 / 250000000000)) := by
  have h := reflection_log_3916_neg
  have he : Real.log (299271885189 / 250000000000) = -Real.log (250000000000 / 299271885189) := by
    rw [show ((299271885189 / 250000000000) : ℝ) = ((250000000000 / 299271885189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3917_neg : (360039517 / 1000000000) ≤ -Real.log (125000000000 / 179173257087) ∧
    -Real.log (125000000000 / 179173257087) ≤ (180019759 / 500000000) := by
  have h := checkLog_sound (w := (54173257087 / 304173257087)) (n := 12)
    (lo := (360039517 / 1000000000)) (hi := (180019759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179173257087 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179173257087 / 125000000000) = 1/(125000000000 / 179173257087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3917 : Bounds (360039517 / 1000000000) (180019759 / 500000000) (Real.log (179173257087 / 125000000000)) := by
  have h := reflection_log_3917_neg
  have he : Real.log (179173257087 / 125000000000) = -Real.log (125000000000 / 179173257087) := by
    rw [show ((179173257087 / 125000000000) : ℝ) = ((125000000000 / 179173257087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3918_neg : (45030759 / 125000000) ≤ -Real.log (100000000000 / 143368216111) ∧
    -Real.log (100000000000 / 143368216111) ≤ (360246073 / 1000000000) := by
  have h := checkLog_sound (w := (43368216111 / 243368216111)) (n := 12)
    (lo := (45030759 / 125000000)) (hi := (360246073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143368216111 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143368216111 / 100000000000) = 1/(100000000000 / 143368216111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3918 : Bounds (45030759 / 125000000) (360246073 / 1000000000) (Real.log (143368216111 / 100000000000)) := by
  have h := reflection_log_3918_neg
  have he : Real.log (143368216111 / 100000000000) = -Real.log (100000000000 / 143368216111) := by
    rw [show ((143368216111 / 100000000000) : ℝ) = ((100000000000 / 143368216111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3919_neg : (164072721 / 1000000000) ≤ -Real.log (10000 / 11783) ∧
    -Real.log (10000 / 11783) ≤ (82036361 / 500000000) := by
  have h := checkLog_sound (w := (1783 / 21783)) (n := 12)
    (lo := (164072721 / 1000000000)) (hi := (82036361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11783 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11783 / 10000) = 1/(10000 / 11783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3919 : Bounds (164072721 / 1000000000) (82036361 / 500000000) (Real.log (11783 / 10000)) := by
  have h := reflection_log_3919_neg
  have he : Real.log (11783 / 10000) = -Real.log (10000 / 11783) := by
    rw [show ((11783 / 10000) : ℝ) = ((10000 / 11783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3920_neg : (98189957 / 500000000) ≤ -Real.log (8217 / 10000) ∧
    -Real.log (8217 / 10000) ≤ (39275983 / 200000000) := by
  have h := checkLog_sound (w := (1783 / 18217)) (n := 12)
    (lo := (98189957 / 500000000)) (hi := (39275983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8217) = 1/(8217 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3920 : Bounds (-39275983 / 200000000) (-98189957 / 500000000) (Real.log (8217 / 10000)) := by
  have h := reflection_log_3920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3921_neg : (44571 / 250000000) ≤ -Real.log (10000000 / 10001783) ∧
    -Real.log (10000000 / 10001783) ≤ (35657 / 200000000) := by
  have h := checkLog_sound (w := (1783 / 20001783)) (n := 12)
    (lo := (44571 / 250000000)) (hi := (35657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001783 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001783 / 10000000) = 1/(10000000 / 10001783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3921 : Bounds (44571 / 250000000) (35657 / 200000000) (Real.log (10001783 / 10000000)) := by
  have h := reflection_log_3921_neg
  have he : Real.log (10001783 / 10000000) = -Real.log (10000000 / 10001783) := by
    rw [show ((10001783 / 10000000) : ℝ) = ((10000000 / 10001783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3922_neg : (35663 / 200000000) ≤ -Real.log (9998217 / 10000000) ∧
    -Real.log (9998217 / 10000000) ≤ (44579 / 250000000) := by
  have h := checkLog_sound (w := (1783 / 19998217)) (n := 12)
    (lo := (35663 / 200000000)) (hi := (44579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998217) = 1/(9998217 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3922 : Bounds (-44579 / 250000000) (-35663 / 200000000) (Real.log (9998217 / 10000000)) := by
  have h := reflection_log_3922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3923_neg : (85742739 / 1000000000) ≤ -Real.log (500000 / 544763) ∧
    -Real.log (500000 / 544763) ≤ (4287137 / 50000000) := by
  have h := checkLog_sound (w := (44763 / 1044763)) (n := 12)
    (lo := (85742739 / 1000000000)) (hi := (4287137 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544763 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544763 / 500000) = 1/(500000 / 544763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3923 : Bounds (85742739 / 1000000000) (4287137 / 50000000) (Real.log (544763 / 500000)) := by
  have h := reflection_log_3923_neg
  have he : Real.log (544763 / 500000) = -Real.log (500000 / 544763) := by
    rw [show ((544763 / 500000) : ℝ) = ((500000 / 544763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3924_neg : (18757987 / 200000000) ≤ -Real.log (455237 / 500000) ∧
    -Real.log (455237 / 500000) ≤ (5861871 / 62500000) := by
  have h := checkLog_sound (w := (44763 / 955237)) (n := 12)
    (lo := (18757987 / 200000000)) (hi := (5861871 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455237) = 1/(455237 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3924 : Bounds (-5861871 / 62500000) (-18757987 / 200000000) (Real.log (455237 / 500000)) := by
  have h := reflection_log_3924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3925_neg : (859529 / 10000000) ≤ -Real.log (200000 / 217951) ∧
    -Real.log (200000 / 217951) ≤ (85952901 / 1000000000) := by
  have h := checkLog_sound (w := (17951 / 417951)) (n := 12)
    (lo := (859529 / 10000000)) (hi := (85952901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217951 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217951 / 200000) = 1/(200000 / 217951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3925 : Bounds (859529 / 10000000) (85952901 / 1000000000) (Real.log (217951 / 200000)) := by
  have h := reflection_log_3925_neg
  have he : Real.log (217951 / 200000) = -Real.log (200000 / 217951) := by
    rw [show ((217951 / 200000) : ℝ) = ((200000 / 217951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3926_neg : (23510371 / 250000000) ≤ -Real.log (182049 / 200000) ∧
    -Real.log (182049 / 200000) ≤ (18808297 / 200000000) := by
  have h := checkLog_sound (w := (17951 / 382049)) (n := 12)
    (lo := (23510371 / 250000000)) (hi := (18808297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182049) = 1/(182049 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3926 : Bounds (-18808297 / 200000000) (-23510371 / 250000000) (Real.log (182049 / 200000)) := by
  have h := reflection_log_3926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3927_neg : (1011073 / 125000000) ≤ -Real.log (39677761599 / 40000000000) ∧
    -Real.log (39677761599 / 40000000000) ≤ (1617717 / 200000000) := by
  have h := checkLog_sound (w := (322238401 / 79677761599)) (n := 12)
    (lo := (1011073 / 125000000)) (hi := (1617717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39677761599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39677761599) = 1/(39677761599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3927 : Bounds (-1617717 / 200000000) (-1011073 / 125000000) (Real.log (39677761599 / 40000000000)) := by
  have h := reflection_log_3927_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3928_neg : (2011799 / 250000000) ≤ -Real.log (247996273831 / 250000000000) ∧
    -Real.log (247996273831 / 250000000000) ≤ (8047197 / 1000000000) := by
  have h := checkLog_sound (w := (2003726169 / 497996273831)) (n := 12)
    (lo := (2011799 / 250000000)) (hi := (8047197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247996273831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247996273831) = 1/(247996273831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3928 : Bounds (-8047197 / 1000000000) (-2011799 / 250000000) (Real.log (247996273831 / 250000000000)) := by
  have h := reflection_log_3928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3929_neg : (7181307 / 40000000) ≤ -Real.log (100000000000 / 119665800451) ∧
    -Real.log (100000000000 / 119665800451) ≤ (44883169 / 250000000) := by
  have h := checkLog_sound (w := (19665800451 / 219665800451)) (n := 12)
    (lo := (7181307 / 40000000)) (hi := (44883169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119665800451 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119665800451 / 100000000000) = 1/(100000000000 / 119665800451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3929 : Bounds (7181307 / 40000000) (44883169 / 250000000) (Real.log (119665800451 / 100000000000)) := by
  have h := reflection_log_3929_neg
  have he : Real.log (119665800451 / 100000000000) = -Real.log (100000000000 / 119665800451) := by
    rw [show ((119665800451 / 100000000000) : ℝ) = ((100000000000 / 119665800451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3930_neg : (35998877 / 200000000) ≤ -Real.log (250000000000 / 299302660273) ∧
    -Real.log (250000000000 / 299302660273) ≤ (89997193 / 500000000) := by
  have h := checkLog_sound (w := (49302660273 / 549302660273)) (n := 12)
    (lo := (35998877 / 200000000)) (hi := (89997193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299302660273 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299302660273 / 250000000000) = 1/(250000000000 / 299302660273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3930 : Bounds (35998877 / 200000000) (89997193 / 500000000) (Real.log (299302660273 / 250000000000)) := by
  have h := reflection_log_3930_neg
  have he : Real.log (299302660273 / 250000000000) = -Real.log (250000000000 / 299302660273) := by
    rw [show ((299302660273 / 250000000000) : ℝ) = ((250000000000 / 299302660273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3931_neg : (45030759 / 125000000) ≤ -Real.log (250000000000 / 358420540277) ∧
    -Real.log (250000000000 / 358420540277) ≤ (360246073 / 1000000000) := by
  have h := checkLog_sound (w := (108420540277 / 608420540277)) (n := 12)
    (lo := (45030759 / 125000000)) (hi := (360246073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358420540277 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358420540277 / 250000000000) = 1/(250000000000 / 358420540277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3931 : Bounds (45030759 / 125000000) (360246073 / 1000000000) (Real.log (358420540277 / 250000000000)) := by
  have h := reflection_log_3931_neg
  have he : Real.log (358420540277 / 250000000000) = -Real.log (250000000000 / 358420540277) := by
    rw [show ((358420540277 / 250000000000) : ℝ) = ((250000000000 / 358420540277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3932_neg : (72090527 / 200000000) ≤ -Real.log (500000000000 / 716989168797) ∧
    -Real.log (500000000000 / 716989168797) ≤ (90113159 / 250000000) := by
  have h := checkLog_sound (w := (216989168797 / 1216989168797)) (n := 12)
    (lo := (72090527 / 200000000)) (hi := (90113159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716989168797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716989168797 / 500000000000) = 1/(500000000000 / 716989168797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3932 : Bounds (72090527 / 200000000) (90113159 / 250000000) (Real.log (716989168797 / 500000000000)) := by
  have h := reflection_log_3932_neg
  have he : Real.log (716989168797 / 500000000000) = -Real.log (500000000000 / 716989168797) := by
    rw [show ((716989168797 / 500000000000) : ℝ) = ((500000000000 / 716989168797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3933_neg : (82078793 / 500000000) ≤ -Real.log (1250 / 1473) ∧
    -Real.log (1250 / 1473) ≤ (164157587 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2723)) (n := 12)
    (lo := (82078793 / 500000000)) (hi := (164157587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473 / 1250) = 1/(1250 / 1473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3933 : Bounds (82078793 / 500000000) (164157587 / 1000000000) (Real.log (1473 / 1250)) := by
  have h := reflection_log_3933_neg
  have he : Real.log (1473 / 1250) = -Real.log (1250 / 1473) := by
    rw [show ((1473 / 1250) : ℝ) = ((1250 / 1473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3934_neg : (9825081 / 50000000) ≤ -Real.log (1027 / 1250) ∧
    -Real.log (1027 / 1250) ≤ (196501621 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2277)) (n := 12)
    (lo := (9825081 / 50000000)) (hi := (196501621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1027) = 1/(1027 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3934 : Bounds (-196501621 / 1000000000) (-9825081 / 50000000) (Real.log (1027 / 1250)) := by
  have h := reflection_log_3934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3935_neg : (11149 / 62500000) ≤ -Real.log (1250000 / 1250223) ∧
    -Real.log (1250000 / 1250223) ≤ (35677 / 200000000) := by
  have h := checkLog_sound (w := (223 / 2500223)) (n := 12)
    (lo := (11149 / 62500000)) (hi := (35677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250223 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250223 / 1250000) = 1/(1250000 / 1250223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3935 : Bounds (11149 / 62500000) (35677 / 200000000) (Real.log (1250223 / 1250000)) := by
  have h := reflection_log_3935_neg
  have he : Real.log (1250223 / 1250000) = -Real.log (1250000 / 1250223) := by
    rw [show ((1250223 / 1250000) : ℝ) = ((1250000 / 1250223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3936_neg : (35683 / 200000000) ≤ -Real.log (1249777 / 1250000) ∧
    -Real.log (1249777 / 1250000) ≤ (11151 / 62500000) := by
  have h := checkLog_sound (w := (223 / 2499777)) (n := 12)
    (lo := (35683 / 200000000)) (hi := (11151 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249777) = 1/(1249777 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3936 : Bounds (-11151 / 62500000) (-35683 / 200000000) (Real.log (1249777 / 1250000)) := by
  have h := reflection_log_3936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3937_neg : (85789547 / 1000000000) ≤ -Real.log (1000000 / 1089577) ∧
    -Real.log (1000000 / 1089577) ≤ (21447387 / 250000000) := by
  have h := checkLog_sound (w := (89577 / 2089577)) (n := 12)
    (lo := (85789547 / 1000000000)) (hi := (21447387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089577 / 1000000) = 1/(1000000 / 1089577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3937 : Bounds (85789547 / 1000000000) (21447387 / 250000000) (Real.log (1089577 / 1000000)) := by
  have h := reflection_log_3937_neg
  have he : Real.log (1089577 / 1000000) = -Real.log (1000000 / 1089577) := by
    rw [show ((1089577 / 1000000) : ℝ) = ((1000000 / 1089577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3938_neg : (1466343 / 15625000) ≤ -Real.log (910423 / 1000000) ∧
    -Real.log (910423 / 1000000) ≤ (93845953 / 1000000000) := by
  have h := checkLog_sound (w := (89577 / 1910423)) (n := 12)
    (lo := (1466343 / 15625000)) (hi := (93845953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910423) = 1/(910423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3938 : Bounds (-93845953 / 1000000000) (-1466343 / 15625000) (Real.log (910423 / 1000000)) := by
  have h := reflection_log_3938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3939_neg : (42999849 / 500000000) ≤ -Real.log (500000 / 544903) ∧
    -Real.log (500000 / 544903) ≤ (85999699 / 1000000000) := by
  have h := checkLog_sound (w := (44903 / 1044903)) (n := 12)
    (lo := (42999849 / 500000000)) (hi := (85999699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544903 / 500000) = 1/(500000 / 544903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3939 : Bounds (42999849 / 500000000) (85999699 / 1000000000) (Real.log (544903 / 500000)) := by
  have h := reflection_log_3939_neg
  have he : Real.log (544903 / 500000) = -Real.log (500000 / 544903) := by
    rw [show ((544903 / 500000) : ℝ) = ((500000 / 544903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3940_neg : (18819503 / 200000000) ≤ -Real.log (455097 / 500000) ∧
    -Real.log (455097 / 500000) ≤ (23524379 / 250000000) := by
  have h := checkLog_sound (w := (44903 / 955097)) (n := 12)
    (lo := (18819503 / 200000000)) (hi := (23524379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455097) = 1/(455097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3940 : Bounds (-23524379 / 250000000) (-18819503 / 200000000) (Real.log (455097 / 500000)) := by
  have h := reflection_log_3940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3941_neg : (1012227 / 125000000) ≤ -Real.log (247983720591 / 250000000000) ∧
    -Real.log (247983720591 / 250000000000) ≤ (8097817 / 1000000000) := by
  have h := checkLog_sound (w := (2016279409 / 497983720591)) (n := 12)
    (lo := (1012227 / 125000000)) (hi := (8097817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247983720591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247983720591) = 1/(247983720591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3941 : Bounds (-8097817 / 1000000000) (-1012227 / 125000000) (Real.log (247983720591 / 250000000000)) := by
  have h := reflection_log_3941_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3942_neg : (2014101 / 250000000) ≤ -Real.log (991975961071 / 1000000000000) ∧
    -Real.log (991975961071 / 1000000000000) ≤ (1611281 / 200000000) := by
  have h := checkLog_sound (w := (8024038929 / 1991975961071)) (n := 12)
    (lo := (2014101 / 250000000)) (hi := (1611281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991975961071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991975961071) = 1/(991975961071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3942 : Bounds (-1611281 / 200000000) (-2014101 / 250000000) (Real.log (991975961071 / 1000000000000)) := by
  have h := reflection_log_3942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3943_neg : (179635499 / 1000000000) ≤ -Real.log (250000000000 / 299195264179) ∧
    -Real.log (250000000000 / 299195264179) ≤ (359271 / 2000000) := by
  have h := checkLog_sound (w := (49195264179 / 549195264179)) (n := 12)
    (lo := (179635499 / 1000000000)) (hi := (359271 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299195264179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299195264179 / 250000000000) = 1/(250000000000 / 299195264179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3943 : Bounds (179635499 / 1000000000) (359271 / 2000000) (Real.log (299195264179 / 250000000000)) := by
  have h := reflection_log_3943_neg
  have he : Real.log (299195264179 / 250000000000) = -Real.log (250000000000 / 299195264179) := by
    rw [show ((299195264179 / 250000000000) : ℝ) = ((250000000000 / 299195264179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3944_neg : (90048607 / 500000000) ≤ -Real.log (500000000000 / 598666877611) ∧
    -Real.log (500000000000 / 598666877611) ≤ (36019443 / 200000000) := by
  have h := checkLog_sound (w := (98666877611 / 1098666877611)) (n := 12)
    (lo := (90048607 / 500000000)) (hi := (36019443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598666877611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598666877611 / 500000000000) = 1/(500000000000 / 598666877611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3944 : Bounds (90048607 / 500000000) (36019443 / 200000000) (Real.log (598666877611 / 500000000000)) := by
  have h := reflection_log_3944_neg
  have he : Real.log (598666877611 / 500000000000) = -Real.log (500000000000 / 598666877611) := by
    rw [show ((598666877611 / 500000000000) : ℝ) = ((500000000000 / 598666877611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3945_neg : (72090527 / 200000000) ≤ -Real.log (125000000000 / 179247292199) ∧
    -Real.log (125000000000 / 179247292199) ≤ (90113159 / 250000000) := by
  have h := checkLog_sound (w := (54247292199 / 304247292199)) (n := 12)
    (lo := (72090527 / 200000000)) (hi := (90113159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179247292199 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179247292199 / 125000000000) = 1/(125000000000 / 179247292199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3945 : Bounds (72090527 / 200000000) (90113159 / 250000000) (Real.log (179247292199 / 125000000000)) := by
  have h := reflection_log_3945_neg
  have he : Real.log (179247292199 / 125000000000) = -Real.log (125000000000 / 179247292199) := by
    rw [show ((179247292199 / 125000000000) : ℝ) = ((125000000000 / 179247292199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3946_neg : (180329603 / 500000000) ≤ -Real.log (500000000000 / 717137293087) ∧
    -Real.log (500000000000 / 717137293087) ≤ (360659207 / 1000000000) := by
  have h := checkLog_sound (w := (217137293087 / 1217137293087)) (n := 12)
    (lo := (180329603 / 500000000)) (hi := (360659207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717137293087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717137293087 / 500000000000) = 1/(500000000000 / 717137293087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3946 : Bounds (180329603 / 500000000) (360659207 / 1000000000) (Real.log (717137293087 / 500000000000)) := by
  have h := reflection_log_3946_neg
  have he : Real.log (717137293087 / 500000000000) = -Real.log (500000000000 / 717137293087) := by
    rw [show ((717137293087 / 500000000000) : ℝ) = ((500000000000 / 717137293087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3947_neg : (164242443 / 1000000000) ≤ -Real.log (2000 / 2357) ∧
    -Real.log (2000 / 2357) ≤ (41060611 / 250000000) := by
  have h := checkLog_sound (w := (357 / 4357)) (n := 12)
    (lo := (164242443 / 1000000000)) (hi := (41060611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2357 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2357 / 2000) = 1/(2000 / 2357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3947 : Bounds (164242443 / 1000000000) (41060611 / 250000000) (Real.log (2357 / 2000)) := by
  have h := reflection_log_3947_neg
  have he : Real.log (2357 / 2000) = -Real.log (2000 / 2357) := by
    rw [show ((2357 / 2000) : ℝ) = ((2000 / 2357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3948_neg : (196623341 / 1000000000) ≤ -Real.log (1643 / 2000) ∧
    -Real.log (1643 / 2000) ≤ (98311671 / 500000000) := by
  have h := checkLog_sound (w := (357 / 3643)) (n := 12)
    (lo := (196623341 / 1000000000)) (hi := (98311671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1643) = 1/(1643 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3948 : Bounds (-98311671 / 500000000) (-196623341 / 1000000000) (Real.log (1643 / 2000)) := by
  have h := reflection_log_3948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3949_neg : (44621 / 250000000) ≤ -Real.log (2000000 / 2000357) ∧
    -Real.log (2000000 / 2000357) ≤ (35697 / 200000000) := by
  have h := checkLog_sound (w := (357 / 4000357)) (n := 12)
    (lo := (44621 / 250000000)) (hi := (35697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000357 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000357 / 2000000) = 1/(2000000 / 2000357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3949 : Bounds (44621 / 250000000) (35697 / 200000000) (Real.log (2000357 / 2000000)) := by
  have h := reflection_log_3949_neg
  have he : Real.log (2000357 / 2000000) = -Real.log (2000000 / 2000357) := by
    rw [show ((2000357 / 2000000) : ℝ) = ((2000000 / 2000357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3950_neg : (35703 / 200000000) ≤ -Real.log (1999643 / 2000000) ∧
    -Real.log (1999643 / 2000000) ≤ (44629 / 250000000) := by
  have h := checkLog_sound (w := (357 / 3999643)) (n := 12)
    (lo := (35703 / 200000000)) (hi := (44629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999643) = 1/(1999643 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3950 : Bounds (-44629 / 250000000) (-35703 / 200000000) (Real.log (1999643 / 2000000)) := by
  have h := reflection_log_3950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3951_neg : (85836353 / 1000000000) ≤ -Real.log (250000 / 272407) ∧
    -Real.log (250000 / 272407) ≤ (42918177 / 500000000) := by
  have h := checkLog_sound (w := (22407 / 522407)) (n := 12)
    (lo := (85836353 / 1000000000)) (hi := (42918177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272407 / 250000) = 1/(250000 / 272407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3951 : Bounds (85836353 / 1000000000) (42918177 / 500000000) (Real.log (272407 / 250000)) := by
  have h := reflection_log_3951_neg
  have he : Real.log (272407 / 250000) = -Real.log (250000 / 272407) := by
    rw [show ((272407 / 250000) : ℝ) = ((250000 / 272407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3952_neg : (93901971 / 1000000000) ≤ -Real.log (227593 / 250000) ∧
    -Real.log (227593 / 250000) ≤ (23475493 / 250000000) := by
  have h := checkLog_sound (w := (22407 / 477593)) (n := 12)
    (lo := (93901971 / 1000000000)) (hi := (23475493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227593) = 1/(227593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3952 : Bounds (-23475493 / 250000000) (-93901971 / 1000000000) (Real.log (227593 / 250000)) := by
  have h := reflection_log_3952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3953_neg : (43023247 / 500000000) ≤ -Real.log (1000000 / 1089857) ∧
    -Real.log (1000000 / 1089857) ≤ (17209299 / 200000000) := by
  have h := checkLog_sound (w := (89857 / 2089857)) (n := 12)
    (lo := (43023247 / 500000000)) (hi := (17209299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089857 / 1000000) = 1/(1000000 / 1089857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3953 : Bounds (43023247 / 500000000) (17209299 / 200000000) (Real.log (1089857 / 1000000)) := by
  have h := reflection_log_3953_neg
  have he : Real.log (1089857 / 1000000) = -Real.log (1000000 / 1089857) := by
    rw [show ((1089857 / 1000000) : ℝ) = ((1000000 / 1089857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3954_neg : (23538387 / 250000000) ≤ -Real.log (910143 / 1000000) ∧
    -Real.log (910143 / 1000000) ≤ (94153549 / 1000000000) := by
  have h := checkLog_sound (w := (89857 / 1910143)) (n := 12)
    (lo := (23538387 / 250000000)) (hi := (94153549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910143) = 1/(910143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3954 : Bounds (-94153549 / 1000000000) (-23538387 / 250000000) (Real.log (910143 / 1000000)) := by
  have h := reflection_log_3954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3955_neg : (8107053 / 1000000000) ≤ -Real.log (991925719551 / 1000000000000) ∧
    -Real.log (991925719551 / 1000000000000) ≤ (4053527 / 500000000) := by
  have h := checkLog_sound (w := (8074280449 / 1991925719551)) (n := 12)
    (lo := (8107053 / 1000000000)) (hi := (4053527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991925719551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991925719551) = 1/(991925719551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3955 : Bounds (-4053527 / 500000000) (-8107053 / 1000000000) (Real.log (991925719551 / 1000000000000)) := by
  have h := reflection_log_3955_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3956_neg : (4032809 / 500000000) ≤ -Real.log (61997926351 / 62500000000) ∧
    -Real.log (61997926351 / 62500000000) ≤ (8065619 / 1000000000) := by
  have h := checkLog_sound (w := (502073649 / 124497926351)) (n := 12)
    (lo := (4032809 / 500000000)) (hi := (8065619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61997926351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61997926351) = 1/(61997926351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3956 : Bounds (-8065619 / 1000000000) (-4032809 / 500000000) (Real.log (61997926351 / 62500000000)) := by
  have h := reflection_log_3956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3957_neg : (7189533 / 40000000) ≤ -Real.log (100000000000 / 119690412271) ∧
    -Real.log (100000000000 / 119690412271) ≤ (89869163 / 500000000) := by
  have h := checkLog_sound (w := (19690412271 / 219690412271)) (n := 12)
    (lo := (7189533 / 40000000)) (hi := (89869163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119690412271 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119690412271 / 100000000000) = 1/(100000000000 / 119690412271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3957 : Bounds (7189533 / 40000000) (89869163 / 500000000) (Real.log (119690412271 / 100000000000)) := by
  have h := reflection_log_3957_neg
  have he : Real.log (119690412271 / 100000000000) = -Real.log (100000000000 / 119690412271) := by
    rw [show ((119690412271 / 100000000000) : ℝ) = ((100000000000 / 119690412271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3958_neg : (180200043 / 1000000000) ≤ -Real.log (20000000000 / 23949137663) ∧
    -Real.log (20000000000 / 23949137663) ≤ (45050011 / 250000000) := by
  have h := checkLog_sound (w := (3949137663 / 43949137663)) (n := 12)
    (lo := (180200043 / 1000000000)) (hi := (45050011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23949137663 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23949137663 / 20000000000) = 1/(20000000000 / 23949137663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3958 : Bounds (180200043 / 1000000000) (45050011 / 250000000) (Real.log (23949137663 / 20000000000)) := by
  have h := reflection_log_3958_neg
  have he : Real.log (23949137663 / 20000000000) = -Real.log (20000000000 / 23949137663) := by
    rw [show ((23949137663 / 20000000000) : ℝ) = ((20000000000 / 23949137663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3959_neg : (180329603 / 500000000) ≤ -Real.log (250000000000 / 358568646543) ∧
    -Real.log (250000000000 / 358568646543) ≤ (360659207 / 1000000000) := by
  have h := checkLog_sound (w := (108568646543 / 608568646543)) (n := 12)
    (lo := (180329603 / 500000000)) (hi := (360659207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358568646543 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358568646543 / 250000000000) = 1/(250000000000 / 358568646543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3959 : Bounds (180329603 / 500000000) (360659207 / 1000000000) (Real.log (358568646543 / 250000000000)) := by
  have h := reflection_log_3959_neg
  have he : Real.log (358568646543 / 250000000000) = -Real.log (250000000000 / 358568646543) := by
    rw [show ((358568646543 / 250000000000) : ℝ) = ((250000000000 / 358568646543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3960_neg : (45108223 / 125000000) ≤ -Real.log (500000000000 / 717285453439) ∧
    -Real.log (500000000000 / 717285453439) ≤ (72173157 / 200000000) := by
  have h := checkLog_sound (w := (217285453439 / 1217285453439)) (n := 12)
    (lo := (45108223 / 125000000)) (hi := (72173157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717285453439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717285453439 / 500000000000) = 1/(500000000000 / 717285453439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3960 : Bounds (45108223 / 125000000) (72173157 / 200000000) (Real.log (717285453439 / 500000000000)) := by
  have h := reflection_log_3960_neg
  have he : Real.log (717285453439 / 500000000000) = -Real.log (500000000000 / 717285453439) := by
    rw [show ((717285453439 / 500000000000) : ℝ) = ((500000000000 / 717285453439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3961_neg : (164327293 / 1000000000) ≤ -Real.log (5000 / 5893) ∧
    -Real.log (5000 / 5893) ≤ (82163647 / 500000000) := by
  have h := checkLog_sound (w := (893 / 10893)) (n := 12)
    (lo := (164327293 / 1000000000)) (hi := (82163647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5893 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5893 / 5000) = 1/(5000 / 5893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3961 : Bounds (164327293 / 1000000000) (82163647 / 500000000) (Real.log (5893 / 5000)) := by
  have h := reflection_log_3961_neg
  have he : Real.log (5893 / 5000) = -Real.log (5000 / 5893) := by
    rw [show ((5893 / 5000) : ℝ) = ((5000 / 5893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3962_neg : (196745077 / 1000000000) ≤ -Real.log (4107 / 5000) ∧
    -Real.log (4107 / 5000) ≤ (98372539 / 500000000) := by
  have h := checkLog_sound (w := (893 / 9107)) (n := 12)
    (lo := (196745077 / 1000000000)) (hi := (98372539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4107) = 1/(4107 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3962 : Bounds (-98372539 / 500000000) (-196745077 / 1000000000) (Real.log (4107 / 5000)) := by
  have h := reflection_log_3962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3963_neg : (22323 / 125000000) ≤ -Real.log (5000000 / 5000893) ∧
    -Real.log (5000000 / 5000893) ≤ (35717 / 200000000) := by
  have h := checkLog_sound (w := (893 / 10000893)) (n := 12)
    (lo := (22323 / 125000000)) (hi := (35717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000893 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000893 / 5000000) = 1/(5000000 / 5000893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3963 : Bounds (22323 / 125000000) (35717 / 200000000) (Real.log (5000893 / 5000000)) := by
  have h := reflection_log_3963_neg
  have he : Real.log (5000893 / 5000000) = -Real.log (5000000 / 5000893) := by
    rw [show ((5000893 / 5000000) : ℝ) = ((5000000 / 5000893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3964_neg : (35723 / 200000000) ≤ -Real.log (4999107 / 5000000) ∧
    -Real.log (4999107 / 5000000) ≤ (22327 / 125000000) := by
  have h := checkLog_sound (w := (893 / 9999107)) (n := 12)
    (lo := (35723 / 200000000)) (hi := (22327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999107) = 1/(4999107 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3964 : Bounds (-22327 / 125000000) (-35723 / 200000000) (Real.log (4999107 / 5000000)) := by
  have h := reflection_log_3964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3965_neg : (85882239 / 1000000000) ≤ -Real.log (500000 / 544839) ∧
    -Real.log (500000 / 544839) ≤ (134191 / 1562500) := by
  have h := checkLog_sound (w := (44839 / 1044839)) (n := 12)
    (lo := (85882239 / 1000000000)) (hi := (134191 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544839 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544839 / 500000) = 1/(500000 / 544839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3965 : Bounds (85882239 / 1000000000) (134191 / 1562500) (Real.log (544839 / 500000)) := by
  have h := reflection_log_3965_neg
  have he : Real.log (544839 / 500000) = -Real.log (500000 / 544839) := by
    rw [show ((544839 / 500000) : ℝ) = ((500000 / 544839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3966_neg : (18791379 / 200000000) ≤ -Real.log (455161 / 500000) ∧
    -Real.log (455161 / 500000) ≤ (2936153 / 31250000) := by
  have h := checkLog_sound (w := (44839 / 955161)) (n := 12)
    (lo := (18791379 / 200000000)) (hi := (2936153 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455161) = 1/(455161 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3966 : Bounds (-2936153 / 31250000) (-18791379 / 200000000) (Real.log (455161 / 500000)) := by
  have h := reflection_log_3966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3967_neg : (86093289 / 1000000000) ≤ -Real.log (250000 / 272477) ∧
    -Real.log (250000 / 272477) ≤ (8609329 / 100000000) := by
  have h := checkLog_sound (w := (22477 / 522477)) (n := 12)
    (lo := (86093289 / 1000000000)) (hi := (8609329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272477 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272477 / 250000) = 1/(250000 / 272477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3967 : Bounds (86093289 / 1000000000) (8609329 / 100000000) (Real.log (272477 / 250000)) := by
  have h := reflection_log_3967_neg
  have he : Real.log (272477 / 250000) = -Real.log (250000 / 272477) := by
    rw [show ((272477 / 250000) : ℝ) = ((250000 / 272477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


