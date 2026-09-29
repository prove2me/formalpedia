-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0088__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0088__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:35:34.162296+00:00
-- url     : https://prove2.me/theorems/677afb4e-b0df-4088-b013-81c1401afaef
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0088 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0089)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0088 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0089)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0088 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0089)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0088 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0089) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0088 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0089).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0088 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5632_neg : (45822189 / 500000000) ≤ -Real.log (40000 / 43839) ∧
    -Real.log (40000 / 43839) ≤ (91644379 / 1000000000) := by
  have h := checkLog_sound (w := (3839 / 83839)) (n := 12)
    (lo := (45822189 / 500000000)) (hi := (91644379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43839 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43839 / 40000) = 1/(40000 / 43839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5632 : Bounds (45822189 / 500000000) (91644379 / 1000000000) (Real.log (43839 / 40000)) := by
  have h := reflection_log_5632_neg
  have he : Real.log (43839 / 40000) = -Real.log (40000 / 43839) := by
    rw [show ((43839 / 40000) : ℝ) = ((40000 / 43839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5633_neg : (12612283 / 125000000) ≤ -Real.log (36161 / 40000) ∧
    -Real.log (36161 / 40000) ≤ (20179653 / 200000000) := by
  have h := checkLog_sound (w := (3839 / 76161)) (n := 12)
    (lo := (12612283 / 125000000)) (hi := (20179653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36161) = 1/(36161 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5633 : Bounds (-20179653 / 200000000) (-12612283 / 125000000) (Real.log (36161 / 40000)) := by
  have h := reflection_log_5633_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5634_neg : (4626943 / 500000000) ≤ -Real.log (1585262079 / 1600000000) ∧
    -Real.log (1585262079 / 1600000000) ≤ (9253887 / 1000000000) := by
  have h := checkLog_sound (w := (14737921 / 3185262079)) (n := 12)
    (lo := (4626943 / 500000000)) (hi := (9253887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1585262079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1585262079) = 1/(1585262079 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5634 : Bounds (-9253887 / 1000000000) (-4626943 / 500000000) (Real.log (1585262079 / 1600000000)) := by
  have h := reflection_log_5634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5635_neg : (1841451 / 200000000) ≤ -Real.log (247708750311 / 250000000000) ∧
    -Real.log (247708750311 / 250000000000) ≤ (1150907 / 125000000) := by
  have h := checkLog_sound (w := (2291249689 / 497708750311)) (n := 12)
    (lo := (1841451 / 200000000)) (hi := (1150907 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247708750311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247708750311) = 1/(247708750311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5635 : Bounds (-1150907 / 125000000) (-1841451 / 200000000) (Real.log (247708750311 / 250000000000)) := by
  have h := reflection_log_5635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5636_neg : (48014043 / 250000000) ≤ -Real.log (500000000000 / 605869290673) ∧
    -Real.log (500000000000 / 605869290673) ≤ (192056173 / 1000000000) := by
  have h := checkLog_sound (w := (105869290673 / 1105869290673)) (n := 12)
    (lo := (48014043 / 250000000)) (hi := (192056173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605869290673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605869290673 / 500000000000) = 1/(500000000000 / 605869290673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5636 : Bounds (48014043 / 250000000) (192056173 / 1000000000) (Real.log (605869290673 / 500000000000)) := by
  have h := reflection_log_5636_neg
  have he : Real.log (605869290673 / 500000000000) = -Real.log (500000000000 / 605869290673) := by
    rw [show ((605869290673 / 500000000000) : ℝ) = ((500000000000 / 605869290673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5637_neg : (96271321 / 500000000) ≤ -Real.log (100000000000 / 121232819889) ∧
    -Real.log (100000000000 / 121232819889) ≤ (192542643 / 1000000000) := by
  have h := checkLog_sound (w := (21232819889 / 221232819889)) (n := 12)
    (lo := (96271321 / 500000000)) (hi := (192542643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121232819889 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121232819889 / 100000000000) = 1/(100000000000 / 121232819889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5637 : Bounds (96271321 / 500000000) (192542643 / 1000000000) (Real.log (121232819889 / 100000000000)) := by
  have h := reflection_log_5637_neg
  have he : Real.log (121232819889 / 100000000000) = -Real.log (100000000000 / 121232819889) := by
    rw [show ((121232819889 / 100000000000) : ℝ) = ((100000000000 / 121232819889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5638_neg : (77100873 / 200000000) ≤ -Real.log (125000000000 / 183794466403) ∧
    -Real.log (125000000000 / 183794466403) ≤ (192752183 / 500000000) := by
  have h := checkLog_sound (w := (58794466403 / 308794466403)) (n := 12)
    (lo := (77100873 / 200000000)) (hi := (192752183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183794466403 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183794466403 / 125000000000) = 1/(125000000000 / 183794466403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5638 : Bounds (77100873 / 200000000) (192752183 / 500000000) (Real.log (183794466403 / 125000000000)) := by
  have h := reflection_log_5638_neg
  have he : Real.log (183794466403 / 125000000000) = -Real.log (125000000000 / 183794466403) := by
    rw [show ((183794466403 / 125000000000) : ℝ) = ((125000000000 / 183794466403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5639_neg : (96427973 / 250000000) ≤ -Real.log (31250000000 / 45958153181) ∧
    -Real.log (31250000000 / 45958153181) ≤ (385711893 / 1000000000) := by
  have h := checkLog_sound (w := (14708153181 / 77208153181)) (n := 12)
    (lo := (96427973 / 250000000)) (hi := (385711893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45958153181 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45958153181 / 31250000000) = 1/(31250000000 / 45958153181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5639 : Bounds (96427973 / 250000000) (385711893 / 1000000000) (Real.log (45958153181 / 31250000000)) := by
  have h := reflection_log_5639_neg
  have he : Real.log (45958153181 / 31250000000) = -Real.log (31250000000 / 45958153181) := by
    rw [show ((45958153181 / 31250000000) : ℝ) = ((31250000000 / 45958153181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5640_neg : (174457381 / 1000000000) ≤ -Real.log (5000 / 5953) ∧
    -Real.log (5000 / 5953) ≤ (87228691 / 500000000) := by
  have h := checkLog_sound (w := (953 / 10953)) (n := 12)
    (lo := (174457381 / 1000000000)) (hi := (87228691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5953 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5953 / 5000) = 1/(5000 / 5953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5640 : Bounds (174457381 / 1000000000) (87228691 / 500000000) (Real.log (5953 / 5000)) := by
  have h := reflection_log_5640_neg
  have he : Real.log (5953 / 5000) = -Real.log (5000 / 5953) := by
    rw [show ((5953 / 5000) : ℝ) = ((5000 / 5953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5641_neg : (105731023 / 500000000) ≤ -Real.log (4047 / 5000) ∧
    -Real.log (4047 / 5000) ≤ (211462047 / 1000000000) := by
  have h := checkLog_sound (w := (953 / 9047)) (n := 12)
    (lo := (105731023 / 500000000)) (hi := (211462047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4047) = 1/(4047 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5641 : Bounds (-211462047 / 1000000000) (-105731023 / 500000000) (Real.log (4047 / 5000)) := by
  have h := reflection_log_5641_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5642_neg : (190581 / 1000000000) ≤ -Real.log (5000000 / 5000953) ∧
    -Real.log (5000000 / 5000953) ≤ (95291 / 500000000) := by
  have h := checkLog_sound (w := (953 / 10000953)) (n := 12)
    (lo := (190581 / 1000000000)) (hi := (95291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000953 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000953 / 5000000) = 1/(5000000 / 5000953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5642 : Bounds (190581 / 1000000000) (95291 / 500000000) (Real.log (5000953 / 5000000)) := by
  have h := reflection_log_5642_neg
  have he : Real.log (5000953 / 5000000) = -Real.log (5000000 / 5000953) := by
    rw [show ((5000953 / 5000000) : ℝ) = ((5000000 / 5000953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5643_neg : (95309 / 500000000) ≤ -Real.log (4999047 / 5000000) ∧
    -Real.log (4999047 / 5000000) ≤ (190619 / 1000000000) := by
  have h := checkLog_sound (w := (953 / 9999047)) (n := 12)
    (lo := (95309 / 500000000)) (hi := (190619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999047) = 1/(4999047 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5643 : Bounds (-190619 / 1000000000) (-95309 / 500000000) (Real.log (4999047 / 5000000)) := by
  have h := reflection_log_5643_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5644_neg : (91471001 / 1000000000) ≤ -Real.log (200000 / 219157) ∧
    -Real.log (200000 / 219157) ≤ (45735501 / 500000000) := by
  have h := checkLog_sound (w := (19157 / 419157)) (n := 12)
    (lo := (91471001 / 1000000000)) (hi := (45735501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219157 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219157 / 200000) = 1/(200000 / 219157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5644 : Bounds (91471001 / 1000000000) (45735501 / 500000000) (Real.log (219157 / 200000)) := by
  have h := reflection_log_5644_neg
  have he : Real.log (219157 / 200000) = -Real.log (200000 / 219157) := by
    rw [show ((219157 / 200000) : ℝ) = ((200000 / 219157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5645_neg : (20137623 / 200000000) ≤ -Real.log (180843 / 200000) ∧
    -Real.log (180843 / 200000) ≤ (25172029 / 250000000) := by
  have h := checkLog_sound (w := (19157 / 380843)) (n := 12)
    (lo := (20137623 / 200000000)) (hi := (25172029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180843) = 1/(180843 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5645 : Bounds (-25172029 / 250000000) (-20137623 / 200000000) (Real.log (180843 / 200000)) := by
  have h := reflection_log_5645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5646_neg : (9169091 / 100000000) ≤ -Real.log (500000 / 548013) ∧
    -Real.log (500000 / 548013) ≤ (91690911 / 1000000000) := by
  have h := checkLog_sound (w := (48013 / 1048013)) (n := 12)
    (lo := (9169091 / 100000000)) (hi := (91690911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548013 / 500000) = 1/(500000 / 548013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5646 : Bounds (9169091 / 100000000) (91690911 / 1000000000) (Real.log (548013 / 500000)) := by
  have h := reflection_log_5646_neg
  have he : Real.log (548013 / 500000) = -Real.log (500000 / 548013) := by
    rw [show ((548013 / 500000) : ℝ) = ((500000 / 548013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5647_neg : (2523867 / 25000000) ≤ -Real.log (451987 / 500000) ∧
    -Real.log (451987 / 500000) ≤ (100954681 / 1000000000) := by
  have h := checkLog_sound (w := (48013 / 951987)) (n := 12)
    (lo := (2523867 / 25000000)) (hi := (100954681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451987) = 1/(451987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5647 : Bounds (-100954681 / 1000000000) (-2523867 / 25000000) (Real.log (451987 / 500000)) := by
  have h := reflection_log_5647_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5648_neg : (9263769 / 1000000000) ≤ -Real.log (247694751831 / 250000000000) ∧
    -Real.log (247694751831 / 250000000000) ≤ (926377 / 100000000) := by
  have h := checkLog_sound (w := (2305248169 / 497694751831)) (n := 12)
    (lo := (9263769 / 1000000000)) (hi := (926377 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247694751831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247694751831) = 1/(247694751831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5648 : Bounds (-926377 / 100000000) (-9263769 / 1000000000) (Real.log (247694751831 / 250000000000)) := by
  have h := reflection_log_5648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5649_neg : (9217113 / 1000000000) ≤ -Real.log (39633009351 / 40000000000) ∧
    -Real.log (39633009351 / 40000000000) ≤ (4608557 / 500000000) := by
  have h := checkLog_sound (w := (366990649 / 79633009351)) (n := 12)
    (lo := (9217113 / 1000000000)) (hi := (4608557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39633009351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39633009351) = 1/(39633009351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5649 : Bounds (-4608557 / 500000000) (-9217113 / 1000000000) (Real.log (39633009351 / 40000000000)) := by
  have h := reflection_log_5649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5650_neg : (48039779 / 250000000) ≤ -Real.log (250000000000 / 302965832241) ∧
    -Real.log (250000000000 / 302965832241) ≤ (192159117 / 1000000000) := by
  have h := checkLog_sound (w := (52965832241 / 552965832241)) (n := 12)
    (lo := (48039779 / 250000000)) (hi := (192159117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302965832241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302965832241 / 250000000000) = 1/(250000000000 / 302965832241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5650 : Bounds (48039779 / 250000000) (192159117 / 1000000000) (Real.log (302965832241 / 250000000000)) := by
  have h := reflection_log_5650_neg
  have he : Real.log (302965832241 / 250000000000) = -Real.log (250000000000 / 302965832241) := by
    rw [show ((302965832241 / 250000000000) : ℝ) = ((250000000000 / 302965832241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5651_neg : (19264559 / 100000000) ≤ -Real.log (100000000000 / 121245301303) ∧
    -Real.log (100000000000 / 121245301303) ≤ (192645591 / 1000000000) := by
  have h := checkLog_sound (w := (21245301303 / 221245301303)) (n := 12)
    (lo := (19264559 / 100000000)) (hi := (192645591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121245301303 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121245301303 / 100000000000) = 1/(100000000000 / 121245301303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5651 : Bounds (19264559 / 100000000) (192645591 / 1000000000) (Real.log (121245301303 / 100000000000)) := by
  have h := reflection_log_5651_neg
  have he : Real.log (121245301303 / 100000000000) = -Real.log (100000000000 / 121245301303) := by
    rw [show ((121245301303 / 100000000000) : ℝ) = ((100000000000 / 121245301303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5652_neg : (96427973 / 250000000) ≤ -Real.log (100000000000 / 147066090179) ∧
    -Real.log (100000000000 / 147066090179) ≤ (385711893 / 1000000000) := by
  have h := checkLog_sound (w := (47066090179 / 247066090179)) (n := 12)
    (lo := (96427973 / 250000000)) (hi := (385711893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147066090179 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147066090179 / 100000000000) = 1/(100000000000 / 147066090179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5652 : Bounds (96427973 / 250000000) (385711893 / 1000000000) (Real.log (147066090179 / 100000000000)) := by
  have h := reflection_log_5652_neg
  have he : Real.log (147066090179 / 100000000000) = -Real.log (100000000000 / 147066090179) := by
    rw [show ((147066090179 / 100000000000) : ℝ) = ((100000000000 / 147066090179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5653_neg : (96479857 / 250000000) ≤ -Real.log (250000000000 / 367741536941) ∧
    -Real.log (250000000000 / 367741536941) ≤ (385919429 / 1000000000) := by
  have h := checkLog_sound (w := (117741536941 / 617741536941)) (n := 12)
    (lo := (96479857 / 250000000)) (hi := (385919429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367741536941 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367741536941 / 250000000000) = 1/(250000000000 / 367741536941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5653 : Bounds (96479857 / 250000000) (385919429 / 1000000000) (Real.log (367741536941 / 250000000000)) := by
  have h := reflection_log_5653_neg
  have he : Real.log (367741536941 / 250000000000) = -Real.log (250000000000 / 367741536941) := by
    rw [show ((367741536941 / 250000000000) : ℝ) = ((250000000000 / 367741536941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5654_neg : (174541369 / 1000000000) ≤ -Real.log (10000 / 11907) ∧
    -Real.log (10000 / 11907) ≤ (17454137 / 100000000) := by
  have h := checkLog_sound (w := (1907 / 21907)) (n := 12)
    (lo := (174541369 / 1000000000)) (hi := (17454137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11907 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11907 / 10000) = 1/(10000 / 11907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5654 : Bounds (174541369 / 1000000000) (17454137 / 100000000) (Real.log (11907 / 10000)) := by
  have h := reflection_log_5654_neg
  have he : Real.log (11907 / 10000) = -Real.log (10000 / 11907) := by
    rw [show ((11907 / 10000) : ℝ) = ((10000 / 11907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5655_neg : (105792801 / 500000000) ≤ -Real.log (8093 / 10000) ∧
    -Real.log (8093 / 10000) ≤ (211585603 / 1000000000) := by
  have h := checkLog_sound (w := (1907 / 18093)) (n := 12)
    (lo := (105792801 / 500000000)) (hi := (211585603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8093) = 1/(8093 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5655 : Bounds (-211585603 / 1000000000) (-105792801 / 500000000) (Real.log (8093 / 10000)) := by
  have h := reflection_log_5655_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5656_neg : (190681 / 1000000000) ≤ -Real.log (10000000 / 10001907) ∧
    -Real.log (10000000 / 10001907) ≤ (95341 / 500000000) := by
  have h := checkLog_sound (w := (1907 / 20001907)) (n := 12)
    (lo := (190681 / 1000000000)) (hi := (95341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001907 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001907 / 10000000) = 1/(10000000 / 10001907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5656 : Bounds (190681 / 1000000000) (95341 / 500000000) (Real.log (10001907 / 10000000)) := by
  have h := reflection_log_5656_neg
  have he : Real.log (10001907 / 10000000) = -Real.log (10000000 / 10001907) := by
    rw [show ((10001907 / 10000000) : ℝ) = ((10000000 / 10001907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5657_neg : (95359 / 500000000) ≤ -Real.log (9998093 / 10000000) ∧
    -Real.log (9998093 / 10000000) ≤ (190719 / 1000000000) := by
  have h := checkLog_sound (w := (1907 / 19998093)) (n := 12)
    (lo := (95359 / 500000000)) (hi := (190719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998093) = 1/(9998093 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5657 : Bounds (-190719 / 1000000000) (-95359 / 500000000) (Real.log (9998093 / 10000000)) := by
  have h := reflection_log_5657_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5658_neg : (45758771 / 500000000) ≤ -Real.log (250000 / 273959) ∧
    -Real.log (250000 / 273959) ≤ (91517543 / 1000000000) := by
  have h := checkLog_sound (w := (23959 / 523959)) (n := 12)
    (lo := (45758771 / 500000000)) (hi := (91517543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273959 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273959 / 250000) = 1/(250000 / 273959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5658 : Bounds (45758771 / 500000000) (91517543 / 1000000000) (Real.log (273959 / 250000)) := by
  have h := reflection_log_5658_neg
  have he : Real.log (273959 / 250000) = -Real.log (250000 / 273959) := by
    rw [show ((273959 / 250000) : ℝ) = ((250000 / 273959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5659_neg : (100744519 / 1000000000) ≤ -Real.log (226041 / 250000) ∧
    -Real.log (226041 / 250000) ≤ (2518613 / 25000000) := by
  have h := checkLog_sound (w := (23959 / 476041)) (n := 12)
    (lo := (100744519 / 1000000000)) (hi := (2518613 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226041) = 1/(226041 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5659 : Bounds (-2518613 / 25000000) (-100744519 / 1000000000) (Real.log (226041 / 250000)) := by
  have h := reflection_log_5659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5660_neg : (91737441 / 1000000000) ≤ -Real.log (1000000 / 1096077) ∧
    -Real.log (1000000 / 1096077) ≤ (45868721 / 500000000) := by
  have h := checkLog_sound (w := (96077 / 2096077)) (n := 12)
    (lo := (91737441 / 1000000000)) (hi := (45868721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096077 / 1000000) = 1/(1000000 / 1096077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5660 : Bounds (91737441 / 1000000000) (45868721 / 500000000) (Real.log (1096077 / 1000000)) := by
  have h := reflection_log_5660_neg
  have he : Real.log (1096077 / 1000000) = -Real.log (1000000 / 1096077) := by
    rw [show ((1096077 / 1000000) : ℝ) = ((1000000 / 1096077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5661_neg : (101011099 / 1000000000) ≤ -Real.log (903923 / 1000000) ∧
    -Real.log (903923 / 1000000) ≤ (1010111 / 10000000) := by
  have h := checkLog_sound (w := (96077 / 1903923)) (n := 12)
    (lo := (101011099 / 1000000000)) (hi := (1010111 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903923) = 1/(903923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5661 : Bounds (-1010111 / 10000000) (-101011099 / 1000000000) (Real.log (903923 / 1000000)) := by
  have h := reflection_log_5661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5662_neg : (9273657 / 1000000000) ≤ -Real.log (990769210071 / 1000000000000) ∧
    -Real.log (990769210071 / 1000000000000) ≤ (4636829 / 500000000) := by
  have h := checkLog_sound (w := (9230789929 / 1990769210071)) (n := 12)
    (lo := (9273657 / 1000000000)) (hi := (4636829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990769210071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990769210071) = 1/(990769210071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5662 : Bounds (-4636829 / 500000000) (-9273657 / 1000000000) (Real.log (990769210071 / 1000000000000)) := by
  have h := reflection_log_5662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5663_neg : (288343 / 31250000) ≤ -Real.log (61925966319 / 62500000000) ∧
    -Real.log (61925966319 / 62500000000) ≤ (9226977 / 1000000000) := by
  have h := checkLog_sound (w := (574033681 / 124425966319)) (n := 12)
    (lo := (288343 / 31250000)) (hi := (9226977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61925966319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61925966319) = 1/(61925966319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5663 : Bounds (-9226977 / 1000000000) (-288343 / 31250000) (Real.log (61925966319 / 62500000000)) := by
  have h := reflection_log_5663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5664_neg : (192262061 / 1000000000) ≤ -Real.log (31250000000 / 37874627833) ∧
    -Real.log (31250000000 / 37874627833) ≤ (96131031 / 500000000) := by
  have h := checkLog_sound (w := (6624627833 / 69124627833)) (n := 12)
    (lo := (192262061 / 1000000000)) (hi := (96131031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37874627833 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37874627833 / 31250000000) = 1/(31250000000 / 37874627833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5664 : Bounds (192262061 / 1000000000) (96131031 / 500000000) (Real.log (37874627833 / 31250000000)) := by
  have h := reflection_log_5664_neg
  have he : Real.log (37874627833 / 31250000000) = -Real.log (31250000000 / 37874627833) := by
    rw [show ((37874627833 / 31250000000) : ℝ) = ((31250000000 / 37874627833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5665_neg : (9637427 / 50000000) ≤ -Real.log (125000000000 / 151572230157) ∧
    -Real.log (125000000000 / 151572230157) ≤ (192748541 / 1000000000) := by
  have h := checkLog_sound (w := (26572230157 / 276572230157)) (n := 12)
    (lo := (9637427 / 50000000)) (hi := (192748541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151572230157 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151572230157 / 125000000000) = 1/(125000000000 / 151572230157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5665 : Bounds (9637427 / 50000000) (192748541 / 1000000000) (Real.log (151572230157 / 125000000000)) := by
  have h := reflection_log_5665_neg
  have he : Real.log (151572230157 / 125000000000) = -Real.log (125000000000 / 151572230157) := by
    rw [show ((151572230157 / 125000000000) : ℝ) = ((125000000000 / 151572230157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5666_neg : (96479857 / 250000000) ≤ -Real.log (500000000000 / 735483073881) ∧
    -Real.log (500000000000 / 735483073881) ≤ (385919429 / 1000000000) := by
  have h := checkLog_sound (w := (235483073881 / 1235483073881)) (n := 12)
    (lo := (96479857 / 250000000)) (hi := (385919429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735483073881 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735483073881 / 500000000000) = 1/(500000000000 / 735483073881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5666 : Bounds (96479857 / 250000000) (385919429 / 1000000000) (Real.log (735483073881 / 500000000000)) := by
  have h := reflection_log_5666_neg
  have he : Real.log (735483073881 / 500000000000) = -Real.log (500000000000 / 735483073881) := by
    rw [show ((735483073881 / 500000000000) : ℝ) = ((500000000000 / 735483073881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5667_neg : (386126971 / 1000000000) ≤ -Real.log (250000000000 / 367817867293) ∧
    -Real.log (250000000000 / 367817867293) ≤ (96531743 / 250000000) := by
  have h := checkLog_sound (w := (117817867293 / 617817867293)) (n := 12)
    (lo := (386126971 / 1000000000)) (hi := (96531743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367817867293 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367817867293 / 250000000000) = 1/(250000000000 / 367817867293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5667 : Bounds (386126971 / 1000000000) (96531743 / 250000000) (Real.log (367817867293 / 250000000000)) := by
  have h := reflection_log_5667_neg
  have he : Real.log (367817867293 / 250000000000) = -Real.log (250000000000 / 367817867293) := by
    rw [show ((367817867293 / 250000000000) : ℝ) = ((250000000000 / 367817867293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5668_neg : (3492507 / 20000000) ≤ -Real.log (2500 / 2977) ∧
    -Real.log (2500 / 2977) ≤ (174625351 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 5477)) (n := 12)
    (lo := (3492507 / 20000000)) (hi := (174625351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2977 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2977 / 2500) = 1/(2500 / 2977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5668 : Bounds (3492507 / 20000000) (174625351 / 1000000000) (Real.log (2977 / 2500)) := by
  have h := reflection_log_5668_neg
  have he : Real.log (2977 / 2500) = -Real.log (2500 / 2977) := by
    rw [show ((2977 / 2500) : ℝ) = ((2500 / 2977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5669_neg : (211709173 / 1000000000) ≤ -Real.log (2023 / 2500) ∧
    -Real.log (2023 / 2500) ≤ (105854587 / 500000000) := by
  have h := checkLog_sound (w := (477 / 4523)) (n := 12)
    (lo := (211709173 / 1000000000)) (hi := (105854587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2023) = 1/(2023 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5669 : Bounds (-105854587 / 500000000) (-211709173 / 1000000000) (Real.log (2023 / 2500)) := by
  have h := reflection_log_5669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5670_neg : (190781 / 1000000000) ≤ -Real.log (2500000 / 2500477) ∧
    -Real.log (2500000 / 2500477) ≤ (95391 / 500000000) := by
  have h := checkLog_sound (w := (477 / 5000477)) (n := 12)
    (lo := (190781 / 1000000000)) (hi := (95391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500477 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500477 / 2500000) = 1/(2500000 / 2500477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5670 : Bounds (190781 / 1000000000) (95391 / 500000000) (Real.log (2500477 / 2500000)) := by
  have h := reflection_log_5670_neg
  have he : Real.log (2500477 / 2500000) = -Real.log (2500000 / 2500477) := by
    rw [show ((2500477 / 2500000) : ℝ) = ((2500000 / 2500477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5671_neg : (95409 / 500000000) ≤ -Real.log (2499523 / 2500000) ∧
    -Real.log (2499523 / 2500000) ≤ (190819 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 4999523)) (n := 12)
    (lo := (95409 / 500000000)) (hi := (190819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499523) = 1/(2499523 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5671 : Bounds (-190819 / 1000000000) (-95409 / 500000000) (Real.log (2499523 / 2500000)) := by
  have h := reflection_log_5671_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5672_neg : (91564081 / 1000000000) ≤ -Real.log (1000000 / 1095887) ∧
    -Real.log (1000000 / 1095887) ≤ (45782041 / 500000000) := by
  have h := checkLog_sound (w := (95887 / 2095887)) (n := 12)
    (lo := (91564081 / 1000000000)) (hi := (45782041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095887 / 1000000) = 1/(1000000 / 1095887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5672 : Bounds (91564081 / 1000000000) (45782041 / 500000000) (Real.log (1095887 / 1000000)) := by
  have h := reflection_log_5672_neg
  have he : Real.log (1095887 / 1000000) = -Real.log (1000000 / 1095887) := by
    rw [show ((1095887 / 1000000) : ℝ) = ((1000000 / 1095887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5673_neg : (50400463 / 500000000) ≤ -Real.log (904113 / 1000000) ∧
    -Real.log (904113 / 1000000) ≤ (100800927 / 1000000000) := by
  have h := checkLog_sound (w := (95887 / 1904113)) (n := 12)
    (lo := (50400463 / 500000000)) (hi := (100800927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904113) = 1/(904113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5673 : Bounds (-100800927 / 1000000000) (-50400463 / 500000000) (Real.log (904113 / 1000000)) := by
  have h := reflection_log_5673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5674_neg : (9178397 / 100000000) ≤ -Real.log (15625 / 17127) ∧
    -Real.log (15625 / 17127) ≤ (91783971 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 16376)) (n := 12)
    (lo := (9178397 / 100000000)) (hi := (91783971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17127 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17127 / 15625) = 1/(15625 / 17127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5674 : Bounds (9178397 / 100000000) (91783971 / 1000000000) (Real.log (17127 / 15625)) := by
  have h := reflection_log_5674_neg
  have he : Real.log (17127 / 15625) = -Real.log (15625 / 17127) := by
    rw [show ((17127 / 15625) : ℝ) = ((15625 / 17127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5675_neg : (101067521 / 1000000000) ≤ -Real.log (14123 / 15625) ∧
    -Real.log (14123 / 15625) ≤ (50533761 / 500000000) := by
  have h := checkLog_sound (w := (751 / 14874)) (n := 12)
    (lo := (101067521 / 1000000000)) (hi := (50533761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14123) = 1/(14123 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5675 : Bounds (-50533761 / 500000000) (-101067521 / 1000000000) (Real.log (14123 / 15625)) := by
  have h := reflection_log_5675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5676_neg : (9283551 / 1000000000) ≤ -Real.log (241884621 / 244140625) ∧
    -Real.log (241884621 / 244140625) ≤ (290111 / 31250000) := by
  have h := checkLog_sound (w := (1128002 / 243012623)) (n := 12)
    (lo := (9283551 / 1000000000)) (hi := (290111 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 241884621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 241884621) = 1/(241884621 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5676 : Bounds (-290111 / 31250000) (-9283551 / 1000000000) (Real.log (241884621 / 244140625)) := by
  have h := reflection_log_5676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5677_neg : (1847369 / 200000000) ≤ -Real.log (990805683231 / 1000000000000) ∧
    -Real.log (990805683231 / 1000000000000) ≤ (4618423 / 500000000) := by
  have h := checkLog_sound (w := (9194316769 / 1990805683231)) (n := 12)
    (lo := (1847369 / 200000000)) (hi := (4618423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990805683231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990805683231) = 1/(990805683231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5677 : Bounds (-4618423 / 500000000) (-1847369 / 200000000) (Real.log (990805683231 / 1000000000000)) := by
  have h := reflection_log_5677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5678_neg : (192365007 / 1000000000) ≤ -Real.log (500000000000 / 606056433211) ∧
    -Real.log (500000000000 / 606056433211) ≤ (12022813 / 62500000) := by
  have h := checkLog_sound (w := (106056433211 / 1106056433211)) (n := 12)
    (lo := (192365007 / 1000000000)) (hi := (12022813 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606056433211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606056433211 / 500000000000) = 1/(500000000000 / 606056433211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5678 : Bounds (192365007 / 1000000000) (12022813 / 62500000) (Real.log (606056433211 / 500000000000)) := by
  have h := reflection_log_5678_neg
  have he : Real.log (606056433211 / 500000000000) = -Real.log (500000000000 / 606056433211) := by
    rw [show ((606056433211 / 500000000000) : ℝ) = ((500000000000 / 606056433211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5679_neg : (192851491 / 1000000000) ≤ -Real.log (500000000000 / 606351341783) ∧
    -Real.log (500000000000 / 606351341783) ≤ (48212873 / 250000000) := by
  have h := checkLog_sound (w := (106351341783 / 1106351341783)) (n := 12)
    (lo := (192851491 / 1000000000)) (hi := (48212873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606351341783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606351341783 / 500000000000) = 1/(500000000000 / 606351341783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5679 : Bounds (192851491 / 1000000000) (48212873 / 250000000) (Real.log (606351341783 / 500000000000)) := by
  have h := reflection_log_5679_neg
  have he : Real.log (606351341783 / 500000000000) = -Real.log (500000000000 / 606351341783) := by
    rw [show ((606351341783 / 500000000000) : ℝ) = ((500000000000 / 606351341783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5680_neg : (386126971 / 1000000000) ≤ -Real.log (100000000000 / 147127146917) ∧
    -Real.log (100000000000 / 147127146917) ≤ (96531743 / 250000000) := by
  have h := checkLog_sound (w := (47127146917 / 247127146917)) (n := 12)
    (lo := (386126971 / 1000000000)) (hi := (96531743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147127146917 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147127146917 / 100000000000) = 1/(100000000000 / 147127146917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5680 : Bounds (386126971 / 1000000000) (96531743 / 250000000) (Real.log (147127146917 / 100000000000)) := by
  have h := reflection_log_5680_neg
  have he : Real.log (147127146917 / 100000000000) = -Real.log (100000000000 / 147127146917) := by
    rw [show ((147127146917 / 100000000000) : ℝ) = ((100000000000 / 147127146917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5681_neg : (386334523 / 1000000000) ≤ -Real.log (500000000000 / 735788433021) ∧
    -Real.log (500000000000 / 735788433021) ≤ (96583631 / 250000000) := by
  have h := checkLog_sound (w := (235788433021 / 1235788433021)) (n := 12)
    (lo := (386334523 / 1000000000)) (hi := (96583631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735788433021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735788433021 / 500000000000) = 1/(500000000000 / 735788433021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5681 : Bounds (386334523 / 1000000000) (96583631 / 250000000) (Real.log (735788433021 / 500000000000)) := by
  have h := reflection_log_5681_neg
  have he : Real.log (735788433021 / 500000000000) = -Real.log (500000000000 / 735788433021) := by
    rw [show ((735788433021 / 500000000000) : ℝ) = ((500000000000 / 735788433021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5682_neg : (174709323 / 1000000000) ≤ -Real.log (10000 / 11909) ∧
    -Real.log (10000 / 11909) ≤ (43677331 / 250000000) := by
  have h := checkLog_sound (w := (1909 / 21909)) (n := 12)
    (lo := (174709323 / 1000000000)) (hi := (43677331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11909 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11909 / 10000) = 1/(10000 / 11909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5682 : Bounds (174709323 / 1000000000) (43677331 / 250000000) (Real.log (11909 / 10000)) := by
  have h := reflection_log_5682_neg
  have he : Real.log (11909 / 10000) = -Real.log (10000 / 11909) := by
    rw [show ((11909 / 10000) : ℝ) = ((10000 / 11909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5683_neg : (5295819 / 25000000) ≤ -Real.log (8091 / 10000) ∧
    -Real.log (8091 / 10000) ≤ (211832761 / 1000000000) := by
  have h := checkLog_sound (w := (1909 / 18091)) (n := 12)
    (lo := (5295819 / 25000000)) (hi := (211832761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8091) = 1/(8091 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5683 : Bounds (-211832761 / 1000000000) (-5295819 / 25000000) (Real.log (8091 / 10000)) := by
  have h := reflection_log_5683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5684_neg : (190881 / 1000000000) ≤ -Real.log (10000000 / 10001909) ∧
    -Real.log (10000000 / 10001909) ≤ (95441 / 500000000) := by
  have h := checkLog_sound (w := (1909 / 20001909)) (n := 12)
    (lo := (190881 / 1000000000)) (hi := (95441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001909 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001909 / 10000000) = 1/(10000000 / 10001909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5684 : Bounds (190881 / 1000000000) (95441 / 500000000) (Real.log (10001909 / 10000000)) := by
  have h := reflection_log_5684_neg
  have he : Real.log (10001909 / 10000000) = -Real.log (10000000 / 10001909) := by
    rw [show ((10001909 / 10000000) : ℝ) = ((10000000 / 10001909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5685_neg : (95459 / 500000000) ≤ -Real.log (9998091 / 10000000) ∧
    -Real.log (9998091 / 10000000) ≤ (190919 / 1000000000) := by
  have h := checkLog_sound (w := (1909 / 19998091)) (n := 12)
    (lo := (95459 / 500000000)) (hi := (190919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998091) = 1/(9998091 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5685 : Bounds (-190919 / 1000000000) (-95459 / 500000000) (Real.log (9998091 / 10000000)) := by
  have h := reflection_log_5685_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5686_neg : (91610617 / 1000000000) ≤ -Real.log (500000 / 547969) ∧
    -Real.log (500000 / 547969) ≤ (45805309 / 500000000) := by
  have h := checkLog_sound (w := (47969 / 1047969)) (n := 12)
    (lo := (91610617 / 1000000000)) (hi := (45805309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547969 / 500000) = 1/(500000 / 547969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5686 : Bounds (91610617 / 1000000000) (45805309 / 500000000) (Real.log (547969 / 500000)) := by
  have h := reflection_log_5686_neg
  have he : Real.log (547969 / 500000) = -Real.log (500000 / 547969) := by
    rw [show ((547969 / 500000) : ℝ) = ((500000 / 547969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5687_neg : (12607167 / 125000000) ≤ -Real.log (452031 / 500000) ∧
    -Real.log (452031 / 500000) ≤ (100857337 / 1000000000) := by
  have h := checkLog_sound (w := (47969 / 952031)) (n := 12)
    (lo := (12607167 / 125000000)) (hi := (100857337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452031) = 1/(452031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5687 : Bounds (-100857337 / 1000000000) (-12607167 / 125000000) (Real.log (452031 / 500000)) := by
  have h := reflection_log_5687_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5688_neg : (2869703 / 31250000) ≤ -Real.log (1000000 / 1096179) ∧
    -Real.log (1000000 / 1096179) ≤ (91830497 / 1000000000) := by
  have h := checkLog_sound (w := (96179 / 2096179)) (n := 12)
    (lo := (2869703 / 31250000)) (hi := (91830497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096179 / 1000000) = 1/(1000000 / 1096179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5688 : Bounds (2869703 / 31250000) (91830497 / 1000000000) (Real.log (1096179 / 1000000)) := by
  have h := reflection_log_5688_neg
  have he : Real.log (1096179 / 1000000) = -Real.log (1000000 / 1096179) := by
    rw [show ((1096179 / 1000000) : ℝ) = ((1000000 / 1096179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5689_neg : (101123947 / 1000000000) ≤ -Real.log (903821 / 1000000) ∧
    -Real.log (903821 / 1000000) ≤ (25280987 / 250000000) := by
  have h := checkLog_sound (w := (96179 / 1903821)) (n := 12)
    (lo := (101123947 / 1000000000)) (hi := (25280987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903821) = 1/(903821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5689 : Bounds (-25280987 / 250000000) (-101123947 / 1000000000) (Real.log (903821 / 1000000)) := by
  have h := reflection_log_5689_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5690_neg : (185869 / 20000000) ≤ -Real.log (990749599959 / 1000000000000) ∧
    -Real.log (990749599959 / 1000000000000) ≤ (9293451 / 1000000000) := by
  have h := checkLog_sound (w := (9250400041 / 1990749599959)) (n := 12)
    (lo := (185869 / 20000000)) (hi := (9293451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990749599959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990749599959) = 1/(990749599959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5690 : Bounds (-9293451 / 1000000000) (-185869 / 20000000) (Real.log (990749599959 / 1000000000000)) := by
  have h := reflection_log_5690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5691_neg : (9246719 / 1000000000) ≤ -Real.log (247698975039 / 250000000000) ∧
    -Real.log (247698975039 / 250000000000) ≤ (3612 / 390625) := by
  have h := checkLog_sound (w := (2301024961 / 497698975039)) (n := 12)
    (lo := (9246719 / 1000000000)) (hi := (3612 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247698975039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247698975039) = 1/(247698975039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5691 : Bounds (-3612 / 390625) (-9246719 / 1000000000) (Real.log (247698975039 / 250000000000)) := by
  have h := reflection_log_5691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5692_neg : (96233977 / 500000000) ≤ -Real.log (500000000000 / 606118828133) ∧
    -Real.log (500000000000 / 606118828133) ≤ (38493591 / 200000000) := by
  have h := checkLog_sound (w := (106118828133 / 1106118828133)) (n := 12)
    (lo := (96233977 / 500000000)) (hi := (38493591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606118828133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606118828133 / 500000000000) = 1/(500000000000 / 606118828133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5692 : Bounds (96233977 / 500000000) (38493591 / 200000000) (Real.log (606118828133 / 500000000000)) := by
  have h := reflection_log_5692_neg
  have he : Real.log (606118828133 / 500000000000) = -Real.log (500000000000 / 606118828133) := by
    rw [show ((606118828133 / 500000000000) : ℝ) = ((500000000000 / 606118828133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5693_neg : (192954443 / 1000000000) ≤ -Real.log (1953125000 / 2368803789) ∧
    -Real.log (1953125000 / 2368803789) ≤ (48238611 / 250000000) := by
  have h := checkLog_sound (w := (415678789 / 4321928789)) (n := 12)
    (lo := (192954443 / 1000000000)) (hi := (48238611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2368803789 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2368803789 / 1953125000) = 1/(1953125000 / 2368803789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5693 : Bounds (192954443 / 1000000000) (48238611 / 250000000) (Real.log (2368803789 / 1953125000)) := by
  have h := reflection_log_5693_neg
  have he : Real.log (2368803789 / 1953125000) = -Real.log (1953125000 / 2368803789) := by
    rw [show ((2368803789 / 1953125000) : ℝ) = ((1953125000 / 2368803789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5694_neg : (386334523 / 1000000000) ≤ -Real.log (25000000000 / 36789421651) ∧
    -Real.log (25000000000 / 36789421651) ≤ (96583631 / 250000000) := by
  have h := checkLog_sound (w := (11789421651 / 61789421651)) (n := 12)
    (lo := (386334523 / 1000000000)) (hi := (96583631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36789421651 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36789421651 / 25000000000) = 1/(25000000000 / 36789421651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5694 : Bounds (386334523 / 1000000000) (96583631 / 250000000) (Real.log (36789421651 / 25000000000)) := by
  have h := reflection_log_5694_neg
  have he : Real.log (36789421651 / 25000000000) = -Real.log (25000000000 / 36789421651) := by
    rw [show ((36789421651 / 25000000000) : ℝ) = ((25000000000 / 36789421651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5695_neg : (386542083 / 1000000000) ≤ -Real.log (500000000000 / 735941169201) ∧
    -Real.log (500000000000 / 735941169201) ≤ (96635521 / 250000000) := by
  have h := checkLog_sound (w := (235941169201 / 1235941169201)) (n := 12)
    (lo := (386542083 / 1000000000)) (hi := (96635521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735941169201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735941169201 / 500000000000) = 1/(500000000000 / 735941169201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5695 : Bounds (386542083 / 1000000000) (96635521 / 250000000) (Real.log (735941169201 / 500000000000)) := by
  have h := reflection_log_5695_neg
  have he : Real.log (735941169201 / 500000000000) = -Real.log (500000000000 / 735941169201) := by
    rw [show ((735941169201 / 500000000000) : ℝ) = ((500000000000 / 735941169201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0089 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5696_neg : (17479329 / 100000000) ≤ -Real.log (1000 / 1191) ∧
    -Real.log (1000 / 1191) ≤ (174793291 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 2191)) (n := 12)
    (lo := (17479329 / 100000000)) (hi := (174793291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191 / 1000) = 1/(1000 / 1191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5696 : Bounds (17479329 / 100000000) (174793291 / 1000000000) (Real.log (1191 / 1000)) := by
  have h := reflection_log_5696_neg
  have he : Real.log (1191 / 1000) = -Real.log (1000 / 1191) := by
    rw [show ((1191 / 1000) : ℝ) = ((1000 / 1191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5697_neg : (211956361 / 1000000000) ≤ -Real.log (809 / 1000) ∧
    -Real.log (809 / 1000) ≤ (105978181 / 500000000) := by
  have h := checkLog_sound (w := (191 / 1809)) (n := 12)
    (lo := (211956361 / 1000000000)) (hi := (105978181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 809) = 1/(809 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5697 : Bounds (-105978181 / 500000000) (-211956361 / 1000000000) (Real.log (809 / 1000)) := by
  have h := reflection_log_5697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5698_neg : (190981 / 1000000000) ≤ -Real.log (1000000 / 1000191) ∧
    -Real.log (1000000 / 1000191) ≤ (95491 / 500000000) := by
  have h := checkLog_sound (w := (191 / 2000191)) (n := 12)
    (lo := (190981 / 1000000000)) (hi := (95491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000191 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000191 / 1000000) = 1/(1000000 / 1000191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5698 : Bounds (190981 / 1000000000) (95491 / 500000000) (Real.log (1000191 / 1000000)) := by
  have h := reflection_log_5698_neg
  have he : Real.log (1000191 / 1000000) = -Real.log (1000000 / 1000191) := by
    rw [show ((1000191 / 1000000) : ℝ) = ((1000000 / 1000191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5699_neg : (95509 / 500000000) ≤ -Real.log (999809 / 1000000) ∧
    -Real.log (999809 / 1000000) ≤ (191019 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1999809)) (n := 12)
    (lo := (95509 / 500000000)) (hi := (191019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999809) = 1/(999809 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5699 : Bounds (-191019 / 1000000000) (-95509 / 500000000) (Real.log (999809 / 1000000)) := by
  have h := reflection_log_5699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5700_neg : (91657151 / 1000000000) ≤ -Real.log (1000000 / 1095989) ∧
    -Real.log (1000000 / 1095989) ≤ (1432143 / 15625000) := by
  have h := checkLog_sound (w := (95989 / 2095989)) (n := 12)
    (lo := (91657151 / 1000000000)) (hi := (1432143 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095989 / 1000000) = 1/(1000000 / 1095989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5700 : Bounds (91657151 / 1000000000) (1432143 / 15625000) (Real.log (1095989 / 1000000)) := by
  have h := reflection_log_5700_neg
  have he : Real.log (1095989 / 1000000) = -Real.log (1000000 / 1095989) := by
    rw [show ((1095989 / 1000000) : ℝ) = ((1000000 / 1095989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5701_neg : (80731 / 800000) ≤ -Real.log (904011 / 1000000) ∧
    -Real.log (904011 / 1000000) ≤ (100913751 / 1000000000) := by
  have h := checkLog_sound (w := (95989 / 1904011)) (n := 12)
    (lo := (80731 / 800000)) (hi := (100913751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904011) = 1/(904011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5701 : Bounds (-100913751 / 1000000000) (-80731 / 800000) (Real.log (904011 / 1000000)) := by
  have h := reflection_log_5701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5702_neg : (4593851 / 50000000) ≤ -Real.log (100000 / 109623) ∧
    -Real.log (100000 / 109623) ≤ (91877021 / 1000000000) := by
  have h := checkLog_sound (w := (9623 / 209623)) (n := 12)
    (lo := (4593851 / 50000000)) (hi := (91877021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109623 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109623 / 100000) = 1/(100000 / 109623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5702 : Bounds (4593851 / 50000000) (91877021 / 1000000000) (Real.log (109623 / 100000)) := by
  have h := reflection_log_5702_neg
  have he : Real.log (109623 / 100000) = -Real.log (100000 / 109623) := by
    rw [show ((109623 / 100000) : ℝ) = ((100000 / 109623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5703_neg : (809443 / 8000000) ≤ -Real.log (90377 / 100000) ∧
    -Real.log (90377 / 100000) ≤ (12647547 / 125000000) := by
  have h := checkLog_sound (w := (9623 / 190377)) (n := 12)
    (lo := (809443 / 8000000)) (hi := (12647547 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90377) = 1/(90377 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5703 : Bounds (-12647547 / 125000000) (-809443 / 8000000) (Real.log (90377 / 100000)) := by
  have h := reflection_log_5703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5704_neg : (1860671 / 200000000) ≤ -Real.log (9907397871 / 10000000000) ∧
    -Real.log (9907397871 / 10000000000) ≤ (2325839 / 250000000) := by
  have h := checkLog_sound (w := (92602129 / 19907397871)) (n := 12)
    (lo := (1860671 / 200000000)) (hi := (2325839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9907397871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9907397871) = 1/(9907397871 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5704 : Bounds (-2325839 / 250000000) (-1860671 / 200000000) (Real.log (9907397871 / 10000000000)) := by
  have h := reflection_log_5704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5705_neg : (4628299 / 500000000) ≤ -Real.log (990786111879 / 1000000000000) ∧
    -Real.log (990786111879 / 1000000000000) ≤ (9256599 / 1000000000) := by
  have h := checkLog_sound (w := (9213888121 / 1990786111879)) (n := 12)
    (lo := (4628299 / 500000000)) (hi := (9256599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990786111879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990786111879) = 1/(990786111879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5705 : Bounds (-9256599 / 1000000000) (-4628299 / 500000000) (Real.log (990786111879 / 1000000000000)) := by
  have h := reflection_log_5705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5706_neg : (96285451 / 500000000) ≤ -Real.log (100000000000 / 121236246019) ∧
    -Real.log (100000000000 / 121236246019) ≤ (192570903 / 1000000000) := by
  have h := checkLog_sound (w := (21236246019 / 221236246019)) (n := 12)
    (lo := (96285451 / 500000000)) (hi := (192570903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121236246019 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121236246019 / 100000000000) = 1/(100000000000 / 121236246019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5706 : Bounds (96285451 / 500000000) (192570903 / 1000000000) (Real.log (121236246019 / 100000000000)) := by
  have h := reflection_log_5706_neg
  have he : Real.log (121236246019 / 100000000000) = -Real.log (100000000000 / 121236246019) := by
    rw [show ((121236246019 / 100000000000) : ℝ) = ((100000000000 / 121236246019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5707_neg : (48264349 / 250000000) ≤ -Real.log (50000000000 / 60647620523) ∧
    -Real.log (50000000000 / 60647620523) ≤ (193057397 / 1000000000) := by
  have h := checkLog_sound (w := (10647620523 / 110647620523)) (n := 12)
    (lo := (48264349 / 250000000)) (hi := (193057397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60647620523 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60647620523 / 50000000000) = 1/(50000000000 / 60647620523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5707 : Bounds (48264349 / 250000000) (193057397 / 1000000000) (Real.log (60647620523 / 50000000000)) := by
  have h := reflection_log_5707_neg
  have he : Real.log (60647620523 / 50000000000) = -Real.log (50000000000 / 60647620523) := by
    rw [show ((60647620523 / 50000000000) : ℝ) = ((50000000000 / 60647620523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5708_neg : (386542083 / 1000000000) ≤ -Real.log (1250000000 / 1839852923) ∧
    -Real.log (1250000000 / 1839852923) ≤ (96635521 / 250000000) := by
  have h := checkLog_sound (w := (589852923 / 3089852923)) (n := 12)
    (lo := (386542083 / 1000000000)) (hi := (96635521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839852923 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839852923 / 1250000000) = 1/(1250000000 / 1839852923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5708 : Bounds (386542083 / 1000000000) (96635521 / 250000000) (Real.log (1839852923 / 1250000000)) := by
  have h := reflection_log_5708_neg
  have he : Real.log (1839852923 / 1250000000) = -Real.log (1250000000 / 1839852923) := by
    rw [show ((1839852923 / 1250000000) : ℝ) = ((1250000000 / 1839852923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5709_neg : (96687413 / 250000000) ≤ -Real.log (25000000000 / 36804697157) ∧
    -Real.log (25000000000 / 36804697157) ≤ (386749653 / 1000000000) := by
  have h := checkLog_sound (w := (11804697157 / 61804697157)) (n := 12)
    (lo := (96687413 / 250000000)) (hi := (386749653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36804697157 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36804697157 / 25000000000) = 1/(25000000000 / 36804697157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5709 : Bounds (96687413 / 250000000) (386749653 / 1000000000) (Real.log (36804697157 / 25000000000)) := by
  have h := reflection_log_5709_neg
  have he : Real.log (36804697157 / 25000000000) = -Real.log (25000000000 / 36804697157) := by
    rw [show ((36804697157 / 25000000000) : ℝ) = ((25000000000 / 36804697157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5710_neg : (174877249 / 1000000000) ≤ -Real.log (10000 / 11911) ∧
    -Real.log (10000 / 11911) ≤ (699509 / 4000000) := by
  have h := checkLog_sound (w := (1911 / 21911)) (n := 12)
    (lo := (174877249 / 1000000000)) (hi := (699509 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11911 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11911 / 10000) = 1/(10000 / 11911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5710 : Bounds (174877249 / 1000000000) (699509 / 4000000) (Real.log (11911 / 10000)) := by
  have h := reflection_log_5710_neg
  have he : Real.log (11911 / 10000) = -Real.log (10000 / 11911) := by
    rw [show ((11911 / 10000) : ℝ) = ((10000 / 11911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5711_neg : (106039989 / 500000000) ≤ -Real.log (8089 / 10000) ∧
    -Real.log (8089 / 10000) ≤ (212079979 / 1000000000) := by
  have h := checkLog_sound (w := (1911 / 18089)) (n := 12)
    (lo := (106039989 / 500000000)) (hi := (212079979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8089) = 1/(8089 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5711 : Bounds (-212079979 / 1000000000) (-106039989 / 500000000) (Real.log (8089 / 10000)) := by
  have h := reflection_log_5711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5712_neg : (191081 / 1000000000) ≤ -Real.log (10000000 / 10001911) ∧
    -Real.log (10000000 / 10001911) ≤ (95541 / 500000000) := by
  have h := checkLog_sound (w := (1911 / 20001911)) (n := 12)
    (lo := (191081 / 1000000000)) (hi := (95541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001911 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001911 / 10000000) = 1/(10000000 / 10001911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5712 : Bounds (191081 / 1000000000) (95541 / 500000000) (Real.log (10001911 / 10000000)) := by
  have h := reflection_log_5712_neg
  have he : Real.log (10001911 / 10000000) = -Real.log (10000000 / 10001911) := by
    rw [show ((10001911 / 10000000) : ℝ) = ((10000000 / 10001911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5713_neg : (95559 / 500000000) ≤ -Real.log (9998089 / 10000000) ∧
    -Real.log (9998089 / 10000000) ≤ (191119 / 1000000000) := by
  have h := checkLog_sound (w := (1911 / 19998089)) (n := 12)
    (lo := (95559 / 500000000)) (hi := (191119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998089) = 1/(9998089 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5713 : Bounds (-191119 / 1000000000) (-95559 / 500000000) (Real.log (9998089 / 10000000)) := by
  have h := reflection_log_5713_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5714_neg : (22925921 / 250000000) ≤ -Real.log (25000 / 27401) ∧
    -Real.log (25000 / 27401) ≤ (18340737 / 200000000) := by
  have h := checkLog_sound (w := (2401 / 52401)) (n := 12)
    (lo := (22925921 / 250000000)) (hi := (18340737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27401 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27401 / 25000) = 1/(25000 / 27401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5714 : Bounds (22925921 / 250000000) (18340737 / 200000000) (Real.log (27401 / 25000)) := by
  have h := reflection_log_5714_neg
  have he : Real.log (27401 / 25000) = -Real.log (25000 / 27401) := by
    rw [show ((27401 / 25000) : ℝ) = ((25000 / 27401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5715_neg : (100970167 / 1000000000) ≤ -Real.log (22599 / 25000) ∧
    -Real.log (22599 / 25000) ≤ (12621271 / 125000000) := by
  have h := checkLog_sound (w := (2401 / 47599)) (n := 12)
    (lo := (100970167 / 1000000000)) (hi := (12621271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22599) = 1/(22599 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5715 : Bounds (-12621271 / 125000000) (-100970167 / 1000000000) (Real.log (22599 / 25000)) := by
  have h := reflection_log_5715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5716_neg : (45961771 / 500000000) ≤ -Real.log (1000000 / 1096281) ∧
    -Real.log (1000000 / 1096281) ≤ (91923543 / 1000000000) := by
  have h := checkLog_sound (w := (96281 / 2096281)) (n := 12)
    (lo := (45961771 / 500000000)) (hi := (91923543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096281 / 1000000) = 1/(1000000 / 1096281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5716 : Bounds (45961771 / 500000000) (91923543 / 1000000000) (Real.log (1096281 / 1000000)) := by
  have h := reflection_log_5716_neg
  have he : Real.log (1096281 / 1000000) = -Real.log (1000000 / 1096281) := by
    rw [show ((1096281 / 1000000) : ℝ) = ((1000000 / 1096281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5717_neg : (101236807 / 1000000000) ≤ -Real.log (903719 / 1000000) ∧
    -Real.log (903719 / 1000000) ≤ (12654601 / 125000000) := by
  have h := checkLog_sound (w := (96281 / 1903719)) (n := 12)
    (lo := (101236807 / 1000000000)) (hi := (12654601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903719) = 1/(903719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5717 : Bounds (-12654601 / 125000000) (-101236807 / 1000000000) (Real.log (903719 / 1000000)) := by
  have h := reflection_log_5717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5718_neg : (1862653 / 200000000) ≤ -Real.log (990729969039 / 1000000000000) ∧
    -Real.log (990729969039 / 1000000000000) ≤ (4656633 / 500000000) := by
  have h := checkLog_sound (w := (9270030961 / 1990729969039)) (n := 12)
    (lo := (1862653 / 200000000)) (hi := (4656633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990729969039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990729969039) = 1/(990729969039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5718 : Bounds (-4656633 / 500000000) (-1862653 / 200000000) (Real.log (990729969039 / 1000000000000)) := by
  have h := reflection_log_5718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5719_neg : (9266483 / 1000000000) ≤ -Real.log (619235199 / 625000000) ∧
    -Real.log (619235199 / 625000000) ≤ (2316621 / 250000000) := by
  have h := checkLog_sound (w := (5764801 / 1244235199)) (n := 12)
    (lo := (9266483 / 1000000000)) (hi := (2316621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 619235199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 619235199) = 1/(619235199 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5719 : Bounds (-2316621 / 250000000) (-9266483 / 1000000000) (Real.log (619235199 / 625000000)) := by
  have h := reflection_log_5719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5720_neg : (192673851 / 1000000000) ≤ -Real.log (500000000000 / 606243639099) ∧
    -Real.log (500000000000 / 606243639099) ≤ (48168463 / 250000000) := by
  have h := checkLog_sound (w := (106243639099 / 1106243639099)) (n := 12)
    (lo := (192673851 / 1000000000)) (hi := (48168463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606243639099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606243639099 / 500000000000) = 1/(500000000000 / 606243639099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5720 : Bounds (192673851 / 1000000000) (48168463 / 250000000) (Real.log (606243639099 / 500000000000)) := by
  have h := reflection_log_5720_neg
  have he : Real.log (606243639099 / 500000000000) = -Real.log (500000000000 / 606243639099) := by
    rw [show ((606243639099 / 500000000000) : ℝ) = ((500000000000 / 606243639099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5721_neg : (3863207 / 20000000) ≤ -Real.log (500000000000 / 606538647523) ∧
    -Real.log (500000000000 / 606538647523) ≤ (193160351 / 1000000000) := by
  have h := checkLog_sound (w := (106538647523 / 1106538647523)) (n := 12)
    (lo := (3863207 / 20000000)) (hi := (193160351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606538647523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606538647523 / 500000000000) = 1/(500000000000 / 606538647523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5721 : Bounds (3863207 / 20000000) (193160351 / 1000000000) (Real.log (606538647523 / 500000000000)) := by
  have h := reflection_log_5721_neg
  have he : Real.log (606538647523 / 500000000000) = -Real.log (500000000000 / 606538647523) := by
    rw [show ((606538647523 / 500000000000) : ℝ) = ((500000000000 / 606538647523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5722_neg : (96687413 / 250000000) ≤ -Real.log (500000000000 / 736093943139) ∧
    -Real.log (500000000000 / 736093943139) ≤ (386749653 / 1000000000) := by
  have h := checkLog_sound (w := (236093943139 / 1236093943139)) (n := 12)
    (lo := (96687413 / 250000000)) (hi := (386749653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736093943139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736093943139 / 500000000000) = 1/(500000000000 / 736093943139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5722 : Bounds (96687413 / 250000000) (386749653 / 1000000000) (Real.log (736093943139 / 500000000000)) := by
  have h := reflection_log_5722_neg
  have he : Real.log (736093943139 / 500000000000) = -Real.log (500000000000 / 736093943139) := by
    rw [show ((736093943139 / 500000000000) : ℝ) = ((500000000000 / 736093943139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5723_neg : (96739307 / 250000000) ≤ -Real.log (500000000000 / 736246754853) ∧
    -Real.log (500000000000 / 736246754853) ≤ (386957229 / 1000000000) := by
  have h := checkLog_sound (w := (236246754853 / 1236246754853)) (n := 12)
    (lo := (96739307 / 250000000)) (hi := (386957229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736246754853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736246754853 / 500000000000) = 1/(500000000000 / 736246754853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5723 : Bounds (96739307 / 250000000) (386957229 / 1000000000) (Real.log (736246754853 / 500000000000)) := by
  have h := reflection_log_5723_neg
  have he : Real.log (736246754853 / 500000000000) = -Real.log (500000000000 / 736246754853) := by
    rw [show ((736246754853 / 500000000000) : ℝ) = ((500000000000 / 736246754853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5724_neg : (87480601 / 500000000) ≤ -Real.log (1250 / 1489) ∧
    -Real.log (1250 / 1489) ≤ (174961203 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2739)) (n := 12)
    (lo := (87480601 / 500000000)) (hi := (174961203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 1250) = 1/(1250 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5724 : Bounds (87480601 / 500000000) (174961203 / 1000000000) (Real.log (1489 / 1250)) := by
  have h := reflection_log_5724_neg
  have he : Real.log (1489 / 1250) = -Real.log (1250 / 1489) := by
    rw [show ((1489 / 1250) : ℝ) = ((1250 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5725_neg : (212203611 / 1000000000) ≤ -Real.log (1011 / 1250) ∧
    -Real.log (1011 / 1250) ≤ (53050903 / 250000000) := by
  have h := checkLog_sound (w := (239 / 2261)) (n := 12)
    (lo := (212203611 / 1000000000)) (hi := (53050903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1011) = 1/(1011 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5725 : Bounds (-53050903 / 250000000) (-212203611 / 1000000000) (Real.log (1011 / 1250)) := by
  have h := reflection_log_5725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5726_neg : (191181 / 1000000000) ≤ -Real.log (1250000 / 1250239) ∧
    -Real.log (1250000 / 1250239) ≤ (95591 / 500000000) := by
  have h := checkLog_sound (w := (239 / 2500239)) (n := 12)
    (lo := (191181 / 1000000000)) (hi := (95591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250239 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250239 / 1250000) = 1/(1250000 / 1250239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5726 : Bounds (191181 / 1000000000) (95591 / 500000000) (Real.log (1250239 / 1250000)) := by
  have h := reflection_log_5726_neg
  have he : Real.log (1250239 / 1250000) = -Real.log (1250000 / 1250239) := by
    rw [show ((1250239 / 1250000) : ℝ) = ((1250000 / 1250239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5727_neg : (95609 / 500000000) ≤ -Real.log (1249761 / 1250000) ∧
    -Real.log (1249761 / 1250000) ≤ (191219 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2499761)) (n := 12)
    (lo := (95609 / 500000000)) (hi := (191219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249761) = 1/(1249761 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5727 : Bounds (-191219 / 1000000000) (-95609 / 500000000) (Real.log (1249761 / 1250000)) := by
  have h := reflection_log_5727_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5728_neg : (45875107 / 500000000) ≤ -Real.log (1000000 / 1096091) ∧
    -Real.log (1000000 / 1096091) ≤ (18350043 / 200000000) := by
  have h := checkLog_sound (w := (96091 / 2096091)) (n := 12)
    (lo := (45875107 / 500000000)) (hi := (18350043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096091 / 1000000) = 1/(1000000 / 1096091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5728 : Bounds (45875107 / 500000000) (18350043 / 200000000) (Real.log (1096091 / 1000000)) := by
  have h := reflection_log_5728_neg
  have he : Real.log (1096091 / 1000000) = -Real.log (1000000 / 1096091) := by
    rw [show ((1096091 / 1000000) : ℝ) = ((1000000 / 1096091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5729_neg : (101026587 / 1000000000) ≤ -Real.log (903909 / 1000000) ∧
    -Real.log (903909 / 1000000) ≤ (25256647 / 250000000) := by
  have h := checkLog_sound (w := (96091 / 1903909)) (n := 12)
    (lo := (101026587 / 1000000000)) (hi := (25256647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903909) = 1/(903909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5729 : Bounds (-25256647 / 250000000) (-101026587 / 1000000000) (Real.log (903909 / 1000000)) := by
  have h := reflection_log_5729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5730_neg : (45985487 / 500000000) ≤ -Real.log (1000000 / 1096333) ∧
    -Real.log (1000000 / 1096333) ≤ (3678839 / 40000000) := by
  have h := checkLog_sound (w := (96333 / 2096333)) (n := 12)
    (lo := (45985487 / 500000000)) (hi := (3678839 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096333 / 1000000) = 1/(1000000 / 1096333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5730 : Bounds (45985487 / 500000000) (3678839 / 40000000) (Real.log (1096333 / 1000000)) := by
  have h := reflection_log_5730_neg
  have he : Real.log (1096333 / 1000000) = -Real.log (1000000 / 1096333) := by
    rw [show ((1096333 / 1000000) : ℝ) = ((1000000 / 1096333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5731_neg : (101294349 / 1000000000) ≤ -Real.log (903667 / 1000000) ∧
    -Real.log (903667 / 1000000) ≤ (2025887 / 20000000) := by
  have h := checkLog_sound (w := (96333 / 1903667)) (n := 12)
    (lo := (101294349 / 1000000000)) (hi := (2025887 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903667) = 1/(903667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5731 : Bounds (-2025887 / 20000000) (-101294349 / 1000000000) (Real.log (903667 / 1000000)) := by
  have h := reflection_log_5731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5732_neg : (4661687 / 500000000) ≤ -Real.log (990719953111 / 1000000000000) ∧
    -Real.log (990719953111 / 1000000000000) ≤ (74587 / 8000000) := by
  have h := checkLog_sound (w := (9280046889 / 1990719953111)) (n := 12)
    (lo := (4661687 / 500000000)) (hi := (74587 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990719953111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990719953111) = 1/(990719953111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5732 : Bounds (-74587 / 8000000) (-4661687 / 500000000) (Real.log (990719953111 / 1000000000000)) := by
  have h := reflection_log_5732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5733_neg : (9276373 / 1000000000) ≤ -Real.log (990766519719 / 1000000000000) ∧
    -Real.log (990766519719 / 1000000000000) ≤ (4638187 / 500000000) := by
  have h := checkLog_sound (w := (9233480281 / 1990766519719)) (n := 12)
    (lo := (9276373 / 1000000000)) (hi := (4638187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990766519719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990766519719) = 1/(990766519719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5733 : Bounds (-4638187 / 500000000) (-9276373 / 1000000000) (Real.log (990766519719 / 1000000000000)) := by
  have h := reflection_log_5733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5734_neg : (192776801 / 1000000000) ≤ -Real.log (62500000000 / 75788256893) ∧
    -Real.log (62500000000 / 75788256893) ≤ (96388401 / 500000000) := by
  have h := checkLog_sound (w := (13288256893 / 138288256893)) (n := 12)
    (lo := (192776801 / 1000000000)) (hi := (96388401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75788256893 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75788256893 / 62500000000) = 1/(62500000000 / 75788256893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5734 : Bounds (192776801 / 1000000000) (96388401 / 500000000) (Real.log (75788256893 / 62500000000)) := by
  have h := reflection_log_5734_neg
  have he : Real.log (75788256893 / 62500000000) = -Real.log (62500000000 / 75788256893) := by
    rw [show ((75788256893 / 62500000000) : ℝ) = ((62500000000 / 75788256893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5735_neg : (193265323 / 1000000000) ≤ -Real.log (500000000000 / 606602321431) ∧
    -Real.log (500000000000 / 606602321431) ≤ (48316331 / 250000000) := by
  have h := checkLog_sound (w := (106602321431 / 1106602321431)) (n := 12)
    (lo := (193265323 / 1000000000)) (hi := (48316331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606602321431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606602321431 / 500000000000) = 1/(500000000000 / 606602321431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5735 : Bounds (193265323 / 1000000000) (48316331 / 250000000) (Real.log (606602321431 / 500000000000)) := by
  have h := reflection_log_5735_neg
  have he : Real.log (606602321431 / 500000000000) = -Real.log (500000000000 / 606602321431) := by
    rw [show ((606602321431 / 500000000000) : ℝ) = ((500000000000 / 606602321431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5736_neg : (96739307 / 250000000) ≤ -Real.log (125000000000 / 184061688713) ∧
    -Real.log (125000000000 / 184061688713) ≤ (386957229 / 1000000000) := by
  have h := checkLog_sound (w := (59061688713 / 309061688713)) (n := 12)
    (lo := (96739307 / 250000000)) (hi := (386957229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184061688713 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184061688713 / 125000000000) = 1/(125000000000 / 184061688713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5736 : Bounds (96739307 / 250000000) (386957229 / 1000000000) (Real.log (184061688713 / 125000000000)) := by
  have h := reflection_log_5736_neg
  have he : Real.log (184061688713 / 125000000000) = -Real.log (125000000000 / 184061688713) := by
    rw [show ((184061688713 / 125000000000) : ℝ) = ((125000000000 / 184061688713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5737_neg : (387164813 / 1000000000) ≤ -Real.log (500000000000 / 736399604353) ∧
    -Real.log (500000000000 / 736399604353) ≤ (193582407 / 500000000) := by
  have h := checkLog_sound (w := (236399604353 / 1236399604353)) (n := 12)
    (lo := (387164813 / 1000000000)) (hi := (193582407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736399604353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736399604353 / 500000000000) = 1/(500000000000 / 736399604353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5737 : Bounds (387164813 / 1000000000) (193582407 / 500000000) (Real.log (736399604353 / 500000000000)) := by
  have h := reflection_log_5737_neg
  have he : Real.log (736399604353 / 500000000000) = -Real.log (500000000000 / 736399604353) := by
    rw [show ((736399604353 / 500000000000) : ℝ) = ((500000000000 / 736399604353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5738_neg : (175045147 / 1000000000) ≤ -Real.log (10000 / 11913) ∧
    -Real.log (10000 / 11913) ≤ (43761287 / 250000000) := by
  have h := checkLog_sound (w := (1913 / 21913)) (n := 12)
    (lo := (175045147 / 1000000000)) (hi := (43761287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11913 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11913 / 10000) = 1/(10000 / 11913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5738 : Bounds (175045147 / 1000000000) (43761287 / 250000000) (Real.log (11913 / 10000)) := by
  have h := reflection_log_5738_neg
  have he : Real.log (11913 / 10000) = -Real.log (10000 / 11913) := by
    rw [show ((11913 / 10000) : ℝ) = ((10000 / 11913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5739_neg : (106163629 / 500000000) ≤ -Real.log (8087 / 10000) ∧
    -Real.log (8087 / 10000) ≤ (212327259 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 18087)) (n := 12)
    (lo := (106163629 / 500000000)) (hi := (212327259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8087) = 1/(8087 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5739 : Bounds (-212327259 / 1000000000) (-106163629 / 500000000) (Real.log (8087 / 10000)) := by
  have h := reflection_log_5739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5740_neg : (191281 / 1000000000) ≤ -Real.log (10000000 / 10001913) ∧
    -Real.log (10000000 / 10001913) ≤ (95641 / 500000000) := by
  have h := checkLog_sound (w := (1913 / 20001913)) (n := 12)
    (lo := (191281 / 1000000000)) (hi := (95641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001913 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001913 / 10000000) = 1/(10000000 / 10001913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5740 : Bounds (191281 / 1000000000) (95641 / 500000000) (Real.log (10001913 / 10000000)) := by
  have h := reflection_log_5740_neg
  have he : Real.log (10001913 / 10000000) = -Real.log (10000000 / 10001913) := by
    rw [show ((10001913 / 10000000) : ℝ) = ((10000000 / 10001913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5741_neg : (95659 / 500000000) ≤ -Real.log (9998087 / 10000000) ∧
    -Real.log (9998087 / 10000000) ≤ (191319 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 19998087)) (n := 12)
    (lo := (95659 / 500000000)) (hi := (191319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998087) = 1/(9998087 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5741 : Bounds (-191319 / 1000000000) (-95659 / 500000000) (Real.log (9998087 / 10000000)) := by
  have h := reflection_log_5741_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5742_neg : (45898371 / 500000000) ≤ -Real.log (500000 / 548071) ∧
    -Real.log (500000 / 548071) ≤ (91796743 / 1000000000) := by
  have h := checkLog_sound (w := (48071 / 1048071)) (n := 12)
    (lo := (45898371 / 500000000)) (hi := (91796743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548071 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548071 / 500000) = 1/(500000 / 548071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5742 : Bounds (45898371 / 500000000) (91796743 / 1000000000) (Real.log (548071 / 500000)) := by
  have h := reflection_log_5742_neg
  have he : Real.log (548071 / 500000) = -Real.log (500000 / 548071) := by
    rw [show ((548071 / 500000) : ℝ) = ((500000 / 548071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5743_neg : (10108301 / 100000000) ≤ -Real.log (451929 / 500000) ∧
    -Real.log (451929 / 500000) ≤ (101083011 / 1000000000) := by
  have h := checkLog_sound (w := (48071 / 951929)) (n := 12)
    (lo := (10108301 / 100000000)) (hi := (101083011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451929) = 1/(451929 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5743 : Bounds (-101083011 / 1000000000) (-10108301 / 100000000) (Real.log (451929 / 500000)) := by
  have h := reflection_log_5743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5744_neg : (23004373 / 250000000) ≤ -Real.log (15625 / 17131) ∧
    -Real.log (15625 / 17131) ≤ (92017493 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 16378)) (n := 12)
    (lo := (23004373 / 250000000)) (hi := (92017493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17131 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17131 / 15625) = 1/(15625 / 17131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5744 : Bounds (23004373 / 250000000) (92017493 / 1000000000) (Real.log (17131 / 15625)) := by
  have h := reflection_log_5744_neg
  have he : Real.log (17131 / 15625) = -Real.log (15625 / 17131) := by
    rw [show ((17131 / 15625) : ℝ) = ((15625 / 17131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5745_neg : (101350787 / 1000000000) ≤ -Real.log (14119 / 15625) ∧
    -Real.log (14119 / 15625) ≤ (25337697 / 250000000) := by
  have h := checkLog_sound (w := (753 / 14872)) (n := 12)
    (lo := (101350787 / 1000000000)) (hi := (25337697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14119) = 1/(14119 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5745 : Bounds (-25337697 / 250000000) (-101350787 / 1000000000) (Real.log (14119 / 15625)) := by
  have h := reflection_log_5745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5746_neg : (1866659 / 200000000) ≤ -Real.log (241872589 / 244140625) ∧
    -Real.log (241872589 / 244140625) ≤ (583331 / 62500000) := by
  have h := checkLog_sound (w := (1134018 / 243006607)) (n := 12)
    (lo := (1866659 / 200000000)) (hi := (583331 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 241872589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 241872589) = 1/(241872589 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5746 : Bounds (-583331 / 62500000) (-1866659 / 200000000) (Real.log (241872589 / 244140625)) := by
  have h := reflection_log_5746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5747_neg : (2321567 / 250000000) ≤ -Real.log (247689178959 / 250000000000) ∧
    -Real.log (247689178959 / 250000000000) ≤ (9286269 / 1000000000) := by
  have h := checkLog_sound (w := (2310821041 / 497689178959)) (n := 12)
    (lo := (2321567 / 250000000)) (hi := (9286269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247689178959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247689178959) = 1/(247689178959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5747 : Bounds (-9286269 / 1000000000) (-2321567 / 250000000) (Real.log (247689178959 / 250000000000)) := by
  have h := reflection_log_5747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5748_neg : (24109969 / 125000000) ≤ -Real.log (250000000000 / 303184239117) ∧
    -Real.log (250000000000 / 303184239117) ≤ (192879753 / 1000000000) := by
  have h := checkLog_sound (w := (53184239117 / 553184239117)) (n := 12)
    (lo := (24109969 / 125000000)) (hi := (192879753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303184239117 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303184239117 / 250000000000) = 1/(250000000000 / 303184239117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5748 : Bounds (24109969 / 125000000) (192879753 / 1000000000) (Real.log (303184239117 / 250000000000)) := by
  have h := reflection_log_5748_neg
  have he : Real.log (303184239117 / 250000000000) = -Real.log (250000000000 / 303184239117) := by
    rw [show ((303184239117 / 250000000000) : ℝ) = ((250000000000 / 303184239117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5749_neg : (193368279 / 1000000000) ≤ -Real.log (500000000000 / 606664777959) ∧
    -Real.log (500000000000 / 606664777959) ≤ (4834207 / 25000000) := by
  have h := checkLog_sound (w := (106664777959 / 1106664777959)) (n := 12)
    (lo := (193368279 / 1000000000)) (hi := (4834207 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606664777959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606664777959 / 500000000000) = 1/(500000000000 / 606664777959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5749 : Bounds (193368279 / 1000000000) (4834207 / 25000000) (Real.log (606664777959 / 500000000000)) := by
  have h := reflection_log_5749_neg
  have he : Real.log (606664777959 / 500000000000) = -Real.log (500000000000 / 606664777959) := by
    rw [show ((606664777959 / 500000000000) : ℝ) = ((500000000000 / 606664777959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5750_neg : (387164813 / 1000000000) ≤ -Real.log (3906250000 / 5753121909) ∧
    -Real.log (3906250000 / 5753121909) ≤ (193582407 / 500000000) := by
  have h := checkLog_sound (w := (1846871909 / 9659371909)) (n := 12)
    (lo := (387164813 / 1000000000)) (hi := (193582407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5753121909 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5753121909 / 3906250000) = 1/(3906250000 / 5753121909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5750 : Bounds (387164813 / 1000000000) (193582407 / 500000000) (Real.log (5753121909 / 3906250000)) := by
  have h := reflection_log_5750_neg
  have he : Real.log (5753121909 / 3906250000) = -Real.log (3906250000 / 5753121909) := by
    rw [show ((5753121909 / 3906250000) : ℝ) = ((3906250000 / 5753121909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5751_neg : (193686203 / 500000000) ≤ -Real.log (250000000000 / 368276245827) ∧
    -Real.log (250000000000 / 368276245827) ≤ (387372407 / 1000000000) := by
  have h := checkLog_sound (w := (118276245827 / 618276245827)) (n := 12)
    (lo := (193686203 / 500000000)) (hi := (387372407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368276245827 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368276245827 / 250000000000) = 1/(250000000000 / 368276245827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5751 : Bounds (193686203 / 500000000) (387372407 / 1000000000) (Real.log (368276245827 / 250000000000)) := by
  have h := reflection_log_5751_neg
  have he : Real.log (368276245827 / 250000000000) = -Real.log (250000000000 / 368276245827) := by
    rw [show ((368276245827 / 250000000000) : ℝ) = ((250000000000 / 368276245827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5752_neg : (87564543 / 500000000) ≤ -Real.log (5000 / 5957) ∧
    -Real.log (5000 / 5957) ≤ (175129087 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 10957)) (n := 12)
    (lo := (87564543 / 500000000)) (hi := (175129087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5957 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5957 / 5000) = 1/(5000 / 5957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5752 : Bounds (87564543 / 500000000) (175129087 / 1000000000) (Real.log (5957 / 5000)) := by
  have h := reflection_log_5752_neg
  have he : Real.log (5957 / 5000) = -Real.log (5000 / 5957) := by
    rw [show ((5957 / 5000) : ℝ) = ((5000 / 5957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5753_neg : (212450921 / 1000000000) ≤ -Real.log (4043 / 5000) ∧
    -Real.log (4043 / 5000) ≤ (106225461 / 500000000) := by
  have h := checkLog_sound (w := (957 / 9043)) (n := 12)
    (lo := (212450921 / 1000000000)) (hi := (106225461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4043) = 1/(4043 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5753 : Bounds (-106225461 / 500000000) (-212450921 / 1000000000) (Real.log (4043 / 5000)) := by
  have h := reflection_log_5753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5754_neg : (191381 / 1000000000) ≤ -Real.log (5000000 / 5000957) ∧
    -Real.log (5000000 / 5000957) ≤ (95691 / 500000000) := by
  have h := checkLog_sound (w := (957 / 10000957)) (n := 12)
    (lo := (191381 / 1000000000)) (hi := (95691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000957 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000957 / 5000000) = 1/(5000000 / 5000957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5754 : Bounds (191381 / 1000000000) (95691 / 500000000) (Real.log (5000957 / 5000000)) := by
  have h := reflection_log_5754_neg
  have he : Real.log (5000957 / 5000000) = -Real.log (5000000 / 5000957) := by
    rw [show ((5000957 / 5000000) : ℝ) = ((5000000 / 5000957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5755_neg : (95709 / 500000000) ≤ -Real.log (4999043 / 5000000) ∧
    -Real.log (4999043 / 5000000) ≤ (191419 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 9999043)) (n := 12)
    (lo := (95709 / 500000000)) (hi := (191419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999043) = 1/(4999043 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5755 : Bounds (-191419 / 1000000000) (-95709 / 500000000) (Real.log (4999043 / 5000000)) := by
  have h := reflection_log_5755_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5756_neg : (91843267 / 1000000000) ≤ -Real.log (1000000 / 1096193) ∧
    -Real.log (1000000 / 1096193) ≤ (22960817 / 250000000) := by
  have h := checkLog_sound (w := (96193 / 2096193)) (n := 12)
    (lo := (91843267 / 1000000000)) (hi := (22960817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096193 / 1000000) = 1/(1000000 / 1096193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5756 : Bounds (91843267 / 1000000000) (22960817 / 250000000) (Real.log (1096193 / 1000000)) := by
  have h := reflection_log_5756_neg
  have he : Real.log (1096193 / 1000000) = -Real.log (1000000 / 1096193) := by
    rw [show ((1096193 / 1000000) : ℝ) = ((1000000 / 1096193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5757_neg : (25284859 / 250000000) ≤ -Real.log (903807 / 1000000) ∧
    -Real.log (903807 / 1000000) ≤ (101139437 / 1000000000) := by
  have h := checkLog_sound (w := (96193 / 1903807)) (n := 12)
    (lo := (25284859 / 250000000)) (hi := (101139437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903807) = 1/(903807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5757 : Bounds (-101139437 / 1000000000) (-25284859 / 250000000) (Real.log (903807 / 1000000)) := by
  have h := reflection_log_5757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5758_neg : (92064007 / 1000000000) ≤ -Real.log (200000 / 219287) ∧
    -Real.log (200000 / 219287) ≤ (11508001 / 125000000) := by
  have h := checkLog_sound (w := (19287 / 419287)) (n := 12)
    (lo := (92064007 / 1000000000)) (hi := (11508001 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219287 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219287 / 200000) = 1/(200000 / 219287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5758 : Bounds (92064007 / 1000000000) (11508001 / 125000000) (Real.log (219287 / 200000)) := by
  have h := reflection_log_5758_neg
  have he : Real.log (219287 / 200000) = -Real.log (200000 / 219287) := by
    rw [show ((219287 / 200000) : ℝ) = ((200000 / 219287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5759_neg : (101407229 / 1000000000) ≤ -Real.log (180713 / 200000) ∧
    -Real.log (180713 / 200000) ≤ (10140723 / 100000000) := by
  have h := checkLog_sound (w := (19287 / 380713)) (n := 12)
    (lo := (101407229 / 1000000000)) (hi := (10140723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180713) = 1/(180713 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5759 : Bounds (-10140723 / 100000000) (-101407229 / 1000000000) (Real.log (180713 / 200000)) := by
  have h := reflection_log_5759_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


