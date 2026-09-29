-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0199__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0199__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T20:54:06.787681+00:00
-- url     : https://prove2.me/theorems/9a162b37-9233-4331-9cad-9066bd896b94
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0199 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0200, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0199 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0200, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0201)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0199 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0200, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0201)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0199 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0200, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0201) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0199 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0200, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0201).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0199 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12736_neg : (541853 / 1000000000) ≤ -Real.log (500000 / 500271) ∧
    -Real.log (500000 / 500271) ≤ (270927 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1000271)) (n := 12)
    (lo := (541853 / 1000000000)) (hi := (270927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500271 / 500000) = 1/(500000 / 500271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12736 : Bounds (541853 / 1000000000) (270927 / 500000000) (Real.log (500271 / 500000)) := by
  have h := reflection_log_12736_neg
  have he : Real.log (500271 / 500000) = -Real.log (500000 / 500271) := by
    rw [show ((500271 / 500000) : ℝ) = ((500000 / 500271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12737_neg : (271073 / 500000000) ≤ -Real.log (499729 / 500000) ∧
    -Real.log (499729 / 500000) ≤ (542147 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 999729)) (n := 12)
    (lo := (271073 / 500000000)) (hi := (542147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499729) = 1/(499729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12737 : Bounds (-542147 / 1000000000) (-271073 / 500000000) (Real.log (499729 / 500000)) := by
  have h := reflection_log_12737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12738_neg : (50112051 / 200000000) ≤ -Real.log (200000 / 256949) ∧
    -Real.log (200000 / 256949) ≤ (978751 / 3906250) := by
  have h := checkLog_sound (w := (56949 / 456949)) (n := 12)
    (lo := (50112051 / 200000000)) (hi := (978751 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256949 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256949 / 200000) = 1/(200000 / 256949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12738 : Bounds (50112051 / 200000000) (978751 / 3906250) (Real.log (256949 / 200000)) := by
  have h := reflection_log_12738_neg
  have he : Real.log (256949 / 200000) = -Real.log (200000 / 256949) := by
    rw [show ((256949 / 200000) : ℝ) = ((200000 / 256949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12739_neg : (83779039 / 250000000) ≤ -Real.log (143051 / 200000) ∧
    -Real.log (143051 / 200000) ≤ (335116157 / 1000000000) := by
  have h := checkLog_sound (w := (56949 / 343051)) (n := 12)
    (lo := (83779039 / 250000000)) (hi := (335116157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 143051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 143051) = 1/(143051 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12739 : Bounds (-335116157 / 1000000000) (-83779039 / 250000000) (Real.log (143051 / 200000)) := by
  have h := reflection_log_12739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12740_neg : (50467603 / 200000000) ≤ -Real.log (1000000 / 1287031) ∧
    -Real.log (1000000 / 1287031) ≤ (7885563 / 31250000) := by
  have h := checkLog_sound (w := (287031 / 2287031)) (n := 12)
    (lo := (50467603 / 200000000)) (hi := (7885563 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287031 / 1000000) = 1/(1000000 / 1287031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12740 : Bounds (50467603 / 200000000) (7885563 / 31250000) (Real.log (1287031 / 1000000)) := by
  have h := reflection_log_12740_neg
  have he : Real.log (1287031 / 1000000) = -Real.log (1000000 / 1287031) := by
    rw [show ((1287031 / 1000000) : ℝ) = ((1000000 / 1287031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12741_neg : (338317337 / 1000000000) ≤ -Real.log (712969 / 1000000) ∧
    -Real.log (712969 / 1000000) ≤ (169158669 / 500000000) := by
  have h := checkLog_sound (w := (287031 / 1712969)) (n := 12)
    (lo := (338317337 / 1000000000)) (hi := (169158669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712969) = 1/(712969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12741 : Bounds (-169158669 / 500000000) (-338317337 / 1000000000) (Real.log (712969 / 1000000)) := by
  have h := reflection_log_12741_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12742_neg : (42989661 / 500000000) ≤ -Real.log (917613205039 / 1000000000000) ∧
    -Real.log (917613205039 / 1000000000000) ≤ (85979323 / 1000000000) := by
  have h := checkLog_sound (w := (82386794961 / 1917613205039)) (n := 12)
    (lo := (42989661 / 500000000)) (hi := (85979323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 917613205039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 917613205039) = 1/(917613205039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12742 : Bounds (-85979323 / 1000000000) (-42989661 / 500000000) (Real.log (917613205039 / 1000000000000)) := by
  have h := reflection_log_12742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12743_neg : (84555901 / 1000000000) ≤ -Real.log (36756811399 / 40000000000) ∧
    -Real.log (36756811399 / 40000000000) ≤ (42277951 / 500000000) := by
  have h := checkLog_sound (w := (3243188601 / 76756811399)) (n := 12)
    (lo := (84555901 / 1000000000)) (hi := (42277951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 36756811399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 36756811399) = 1/(36756811399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12743 : Bounds (-42277951 / 500000000) (-84555901 / 1000000000) (Real.log (36756811399 / 40000000000)) := by
  have h := reflection_log_12743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12744_neg : (585676411 / 1000000000) ≤ -Real.log (250000000000 / 449051387267) ∧
    -Real.log (250000000000 / 449051387267) ≤ (146419103 / 250000000) := by
  have h := checkLog_sound (w := (199051387267 / 699051387267)) (n := 12)
    (lo := (585676411 / 1000000000)) (hi := (146419103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449051387267 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449051387267 / 250000000000) = 1/(250000000000 / 449051387267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12744 : Bounds (585676411 / 1000000000) (146419103 / 250000000) (Real.log (449051387267 / 250000000000)) := by
  have h := reflection_log_12744_neg
  have he : Real.log (449051387267 / 250000000000) = -Real.log (250000000000 / 449051387267) := by
    rw [show ((449051387267 / 250000000000) : ℝ) = ((250000000000 / 449051387267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12745_neg : (590655353 / 1000000000) ≤ -Real.log (500000000000 / 902585526159) ∧
    -Real.log (500000000000 / 902585526159) ≤ (295327677 / 500000000) := by
  have h := checkLog_sound (w := (402585526159 / 1402585526159)) (n := 12)
    (lo := (590655353 / 1000000000)) (hi := (295327677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902585526159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902585526159 / 500000000000) = 1/(500000000000 / 902585526159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12745 : Bounds (590655353 / 1000000000) (295327677 / 500000000) (Real.log (902585526159 / 500000000000)) := by
  have h := reflection_log_12745_neg
  have he : Real.log (902585526159 / 500000000000) = -Real.log (500000000000 / 902585526159) := by
    rw [show ((902585526159 / 500000000000) : ℝ) = ((500000000000 / 902585526159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12746_neg : (120549009 / 100000000) ≤ -Real.log (500000000000 / 1669197396963) ∧
    -Real.log (500000000000 / 1669197396963) ≤ (301372523 / 250000000) := by
  have h := checkLog_sound (w := (669197396963 / 2669197396963)) (n := 12)
    (lo := (51234291 / 100000000)) (hi := (512342911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1669197396963 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1669197396963 / 1000000000000) = 1/(500000000000 / 1669197396963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12746 : Bounds (120549009 / 100000000) (301372523 / 250000000) (Real.log (1669197396963 / 500000000000)) := by
  have h := reflection_log_12746_neg
  have he : Real.log (1669197396963 / 500000000000) = -Real.log (500000000000 / 1669197396963) := by
    rw [show ((1669197396963 / 500000000000) : ℝ) = ((500000000000 / 1669197396963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12747_neg : (1213966369 / 1000000000) ≤ -Real.log (250000000000 / 841703056769) ∧
    -Real.log (250000000000 / 841703056769) ≤ (1213966371 / 1000000000) := by
  have h := checkLog_sound (w := (341703056769 / 1341703056769)) (n := 12)
    (lo := (520819189 / 1000000000)) (hi := (52081919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841703056769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(841703056769 / 500000000000) = 1/(250000000000 / 841703056769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12747 : Bounds (1213966369 / 1000000000) (1213966371 / 1000000000) (Real.log (841703056769 / 250000000000)) := by
  have h := reflection_log_12747_neg
  have he : Real.log (841703056769 / 250000000000) = -Real.log (250000000000 / 841703056769) := by
    rw [show ((841703056769 / 250000000000) : ℝ) = ((250000000000 / 841703056769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12748_neg : (43502391 / 100000000) ≤ -Real.log (200 / 309) ∧
    -Real.log (200 / 309) ≤ (435023911 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 509)) (n := 12)
    (lo := (43502391 / 100000000)) (hi := (435023911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 200) = 1/(200 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12748 : Bounds (43502391 / 100000000) (435023911 / 1000000000) (Real.log (309 / 200)) := by
  have h := reflection_log_12748_neg
  have he : Real.log (309 / 200) = -Real.log (200 / 309) := by
    rw [show ((309 / 200) : ℝ) = ((200 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12749_neg : (787457859 / 1000000000) ≤ -Real.log (91 / 200) ∧
    -Real.log (91 / 200) ≤ (787457861 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 191)) (n := 12)
    (lo := (94310679 / 1000000000)) (hi := (2357767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 91) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 91) = 1/(91 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12749 : Bounds (-787457861 / 1000000000) (-787457859 / 1000000000) (Real.log (91 / 200)) := by
  have h := reflection_log_12749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12750_neg : (544851 / 1000000000) ≤ -Real.log (200000 / 200109) ∧
    -Real.log (200000 / 200109) ≤ (136213 / 250000000) := by
  have h := checkLog_sound (w := (109 / 400109)) (n := 12)
    (lo := (544851 / 1000000000)) (hi := (136213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200109 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200109 / 200000) = 1/(200000 / 200109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12750 : Bounds (544851 / 1000000000) (136213 / 250000000) (Real.log (200109 / 200000)) := by
  have h := reflection_log_12750_neg
  have he : Real.log (200109 / 200000) = -Real.log (200000 / 200109) := by
    rw [show ((200109 / 200000) : ℝ) = ((200000 / 200109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12751_neg : (136287 / 250000000) ≤ -Real.log (199891 / 200000) ∧
    -Real.log (199891 / 200000) ≤ (545149 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 399891)) (n := 12)
    (lo := (136287 / 250000000)) (hi := (545149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199891) = 1/(199891 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12751 : Bounds (-545149 / 1000000000) (-136287 / 250000000) (Real.log (199891 / 200000)) := by
  have h := reflection_log_12751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12752_neg : (251942453 / 1000000000) ≤ -Real.log (500000 / 643261) ∧
    -Real.log (500000 / 643261) ≤ (125971227 / 500000000) := by
  have h := checkLog_sound (w := (143261 / 1143261)) (n := 12)
    (lo := (251942453 / 1000000000)) (hi := (125971227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643261 / 500000) = 1/(500000 / 643261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12752 : Bounds (251942453 / 1000000000) (125971227 / 500000000) (Real.log (643261 / 500000)) := by
  have h := reflection_log_12752_neg
  have he : Real.log (643261 / 500000) = -Real.log (500000 / 643261) := by
    rw [show ((643261 / 500000) : ℝ) = ((500000 / 643261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12753_neg : (84400919 / 250000000) ≤ -Real.log (356739 / 500000) ∧
    -Real.log (356739 / 500000) ≤ (337603677 / 1000000000) := by
  have h := checkLog_sound (w := (143261 / 856739)) (n := 12)
    (lo := (84400919 / 250000000)) (hi := (337603677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 356739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 356739) = 1/(356739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12753 : Bounds (-337603677 / 1000000000) (-84400919 / 250000000) (Real.log (356739 / 500000)) := by
  have h := reflection_log_12753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12754_neg : (50744483 / 200000000) ≤ -Real.log (500000 / 644407) ∧
    -Real.log (500000 / 644407) ≤ (15857651 / 62500000) := by
  have h := checkLog_sound (w := (144407 / 1144407)) (n := 12)
    (lo := (50744483 / 200000000)) (hi := (15857651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644407 / 500000) = 1/(500000 / 644407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12754 : Bounds (50744483 / 200000000) (15857651 / 62500000) (Real.log (644407 / 500000)) := by
  have h := reflection_log_12754_neg
  have he : Real.log (644407 / 500000) = -Real.log (500000 / 644407) := by
    rw [show ((644407 / 500000) : ℝ) = ((500000 / 644407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12755_neg : (2130133 / 6250000) ≤ -Real.log (355593 / 500000) ∧
    -Real.log (355593 / 500000) ≤ (340821281 / 1000000000) := by
  have h := checkLog_sound (w := (144407 / 855593)) (n := 12)
    (lo := (2130133 / 6250000)) (hi := (340821281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 355593) = 1/(355593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12755 : Bounds (-340821281 / 1000000000) (-2130133 / 6250000) (Real.log (355593 / 500000)) := by
  have h := reflection_log_12755_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12756_neg : (5443679 / 62500000) ≤ -Real.log (229146618351 / 250000000000) ∧
    -Real.log (229146618351 / 250000000000) ≤ (17419773 / 200000000) := by
  have h := checkLog_sound (w := (20853381649 / 479146618351)) (n := 12)
    (lo := (5443679 / 62500000)) (hi := (17419773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 229146618351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 229146618351) = 1/(229146618351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12756 : Bounds (-17419773 / 200000000) (-5443679 / 62500000) (Real.log (229146618351 / 250000000000)) := by
  have h := reflection_log_12756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12757_neg : (85661223 / 1000000000) ≤ -Real.log (229476285879 / 250000000000) ∧
    -Real.log (229476285879 / 250000000000) ≤ (10707653 / 125000000) := by
  have h := checkLog_sound (w := (20523714121 / 479476285879)) (n := 12)
    (lo := (85661223 / 1000000000)) (hi := (10707653 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 229476285879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 229476285879) = 1/(229476285879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12757 : Bounds (-10707653 / 125000000) (-85661223 / 1000000000) (Real.log (229476285879 / 250000000000)) := by
  have h := reflection_log_12757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12758_neg : (589546129 / 1000000000) ≤ -Real.log (250000000000 / 450792456109) ∧
    -Real.log (250000000000 / 450792456109) ≤ (58954613 / 100000000) := by
  have h := checkLog_sound (w := (200792456109 / 700792456109)) (n := 12)
    (lo := (589546129 / 1000000000)) (hi := (58954613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450792456109 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450792456109 / 250000000000) = 1/(250000000000 / 450792456109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12758 : Bounds (589546129 / 1000000000) (58954613 / 100000000) (Real.log (450792456109 / 250000000000)) := by
  have h := reflection_log_12758_neg
  have he : Real.log (450792456109 / 250000000000) = -Real.log (250000000000 / 450792456109) := by
    rw [show ((450792456109 / 250000000000) : ℝ) = ((250000000000 / 450792456109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12759_neg : (118908739 / 200000000) ≤ -Real.log (125000000000 / 226525479973) ∧
    -Real.log (125000000000 / 226525479973) ≤ (37158981 / 62500000) := by
  have h := checkLog_sound (w := (101525479973 / 351525479973)) (n := 12)
    (lo := (118908739 / 200000000)) (hi := (37158981 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226525479973 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226525479973 / 125000000000) = 1/(125000000000 / 226525479973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12759 : Bounds (118908739 / 200000000) (37158981 / 62500000) (Real.log (226525479973 / 125000000000)) := by
  have h := reflection_log_12759_neg
  have he : Real.log (226525479973 / 125000000000) = -Real.log (125000000000 / 226525479973) := by
    rw [show ((226525479973 / 125000000000) : ℝ) = ((125000000000 / 226525479973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12760_neg : (1213966369 / 1000000000) ≤ -Real.log (500000000000 / 1683406113537) ∧
    -Real.log (500000000000 / 1683406113537) ≤ (1213966371 / 1000000000) := by
  have h := checkLog_sound (w := (683406113537 / 2683406113537)) (n := 12)
    (lo := (520819189 / 1000000000)) (hi := (52081919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683406113537 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1683406113537 / 1000000000000) = 1/(500000000000 / 1683406113537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12760 : Bounds (1213966369 / 1000000000) (1213966371 / 1000000000) (Real.log (1683406113537 / 500000000000)) := by
  have h := reflection_log_12760_neg
  have he : Real.log (1683406113537 / 500000000000) = -Real.log (500000000000 / 1683406113537) := by
    rw [show ((1683406113537 / 500000000000) : ℝ) = ((500000000000 / 1683406113537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12761_neg : (1222481769 / 1000000000) ≤ -Real.log (500000000000 / 1697802197803) ∧
    -Real.log (500000000000 / 1697802197803) ≤ (1222481771 / 1000000000) := by
  have h := checkLog_sound (w := (697802197803 / 2697802197803)) (n := 12)
    (lo := (529334589 / 1000000000)) (hi := (52933459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697802197803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1697802197803 / 1000000000000) = 1/(500000000000 / 1697802197803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12761 : Bounds (1222481769 / 1000000000) (1222481771 / 1000000000) (Real.log (1697802197803 / 500000000000)) := by
  have h := reflection_log_12761_neg
  have he : Real.log (1697802197803 / 500000000000) = -Real.log (500000000000 / 1697802197803) := by
    rw [show ((1697802197803 / 500000000000) : ℝ) = ((500000000000 / 1697802197803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12762_neg : (17478551 / 40000000) ≤ -Real.log (250 / 387) ∧
    -Real.log (250 / 387) ≤ (6827559 / 15625000) := by
  have h := checkLog_sound (w := (137 / 637)) (n := 12)
    (lo := (17478551 / 40000000)) (hi := (6827559 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 250) = 1/(250 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12762 : Bounds (17478551 / 40000000) (6827559 / 15625000) (Real.log (387 / 250)) := by
  have h := reflection_log_12762_neg
  have he : Real.log (387 / 250) = -Real.log (250 / 387) := by
    rw [show ((387 / 250) : ℝ) = ((250 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12763_neg : (397036549 / 500000000) ≤ -Real.log (113 / 250) ∧
    -Real.log (113 / 250) ≤ (7940731 / 10000000) := by
  have h := checkLog_sound (w := (6 / 119)) (n := 12)
    (lo := (50462959 / 500000000)) (hi := (100925919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 113) = 1/(113 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12763 : Bounds (-7940731 / 10000000) (-397036549 / 500000000) (Real.log (113 / 250)) := by
  have h := reflection_log_12763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12764_neg : (547849 / 1000000000) ≤ -Real.log (250000 / 250137) ∧
    -Real.log (250000 / 250137) ≤ (10957 / 20000000) := by
  have h := checkLog_sound (w := (137 / 500137)) (n := 12)
    (lo := (547849 / 1000000000)) (hi := (10957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250137 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250137 / 250000) = 1/(250000 / 250137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12764 : Bounds (547849 / 1000000000) (10957 / 20000000) (Real.log (250137 / 250000)) := by
  have h := reflection_log_12764_neg
  have he : Real.log (250137 / 250000) = -Real.log (250000 / 250137) := by
    rw [show ((250137 / 250000) : ℝ) = ((250000 / 250137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12765_neg : (10963 / 20000000) ≤ -Real.log (249863 / 250000) ∧
    -Real.log (249863 / 250000) ≤ (548151 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 499863)) (n := 12)
    (lo := (10963 / 20000000)) (hi := (548151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249863) = 1/(249863 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12765 : Bounds (-548151 / 1000000000) (-10963 / 20000000) (Real.log (249863 / 250000)) := by
  have h := reflection_log_12765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12766_neg : (31665731 / 125000000) ≤ -Real.log (1000000 / 1288303) ∧
    -Real.log (1000000 / 1288303) ≤ (253325849 / 1000000000) := by
  have h := checkLog_sound (w := (288303 / 2288303)) (n := 12)
    (lo := (31665731 / 125000000)) (hi := (253325849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1288303 / 1000000) = 1/(1000000 / 1288303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12766 : Bounds (31665731 / 125000000) (253325849 / 1000000000) (Real.log (1288303 / 1000000)) := by
  have h := reflection_log_12766_neg
  have he : Real.log (1288303 / 1000000) = -Real.log (1000000 / 1288303) := by
    rw [show ((1288303 / 1000000) : ℝ) = ((1000000 / 1288303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12767_neg : (340103019 / 1000000000) ≤ -Real.log (711697 / 1000000) ∧
    -Real.log (711697 / 1000000) ≤ (17005151 / 50000000) := by
  have h := checkLog_sound (w := (288303 / 1711697)) (n := 12)
    (lo := (340103019 / 1000000000)) (hi := (17005151 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 711697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 711697) = 1/(711697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12767 : Bounds (-17005151 / 50000000) (-340103019 / 1000000000) (Real.log (711697 / 1000000)) := by
  have h := reflection_log_12767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12768_neg : (255108001 / 1000000000) ≤ -Real.log (1000000 / 1290601) ∧
    -Real.log (1000000 / 1290601) ≤ (127554001 / 500000000) := by
  have h := checkLog_sound (w := (290601 / 2290601)) (n := 12)
    (lo := (255108001 / 1000000000)) (hi := (127554001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290601 / 1000000) = 1/(1000000 / 1290601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12768 : Bounds (255108001 / 1000000000) (127554001 / 500000000) (Real.log (1290601 / 1000000)) := by
  have h := reflection_log_12768_neg
  have he : Real.log (1290601 / 1000000) = -Real.log (1000000 / 1290601) := by
    rw [show ((1290601 / 1000000) : ℝ) = ((1000000 / 1290601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12769_neg : (171668573 / 500000000) ≤ -Real.log (709399 / 1000000) ∧
    -Real.log (709399 / 1000000) ≤ (343337147 / 1000000000) := by
  have h := checkLog_sound (w := (290601 / 1709399)) (n := 12)
    (lo := (171668573 / 500000000)) (hi := (343337147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709399) = 1/(709399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12769 : Bounds (-343337147 / 1000000000) (-171668573 / 500000000) (Real.log (709399 / 1000000)) := by
  have h := reflection_log_12769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12770_neg : (11028643 / 125000000) ≤ -Real.log (915551058799 / 1000000000000) ∧
    -Real.log (915551058799 / 1000000000000) ≤ (17645829 / 200000000) := by
  have h := checkLog_sound (w := (84448941201 / 1915551058799)) (n := 12)
    (lo := (11028643 / 125000000)) (hi := (17645829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 915551058799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 915551058799) = 1/(915551058799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12770 : Bounds (-17645829 / 200000000) (-11028643 / 125000000) (Real.log (915551058799 / 1000000000000)) := by
  have h := reflection_log_12770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12771_neg : (86777171 / 1000000000) ≤ -Real.log (916881380191 / 1000000000000) ∧
    -Real.log (916881380191 / 1000000000000) ≤ (21694293 / 250000000) := by
  have h := checkLog_sound (w := (83118619809 / 1916881380191)) (n := 12)
    (lo := (86777171 / 1000000000)) (hi := (21694293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 916881380191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 916881380191) = 1/(916881380191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12771 : Bounds (-21694293 / 250000000) (-86777171 / 1000000000) (Real.log (916881380191 / 1000000000000)) := by
  have h := reflection_log_12771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12772_neg : (148357217 / 250000000) ≤ -Real.log (250000000000 / 452546167821) ∧
    -Real.log (250000000000 / 452546167821) ≤ (593428869 / 1000000000) := by
  have h := checkLog_sound (w := (202546167821 / 702546167821)) (n := 12)
    (lo := (148357217 / 250000000)) (hi := (593428869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((452546167821 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(452546167821 / 250000000000) = 1/(250000000000 / 452546167821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12772 : Bounds (148357217 / 250000000) (593428869 / 1000000000) (Real.log (452546167821 / 250000000000)) := by
  have h := reflection_log_12772_neg
  have he : Real.log (452546167821 / 250000000000) = -Real.log (250000000000 / 452546167821) := by
    rw [show ((452546167821 / 250000000000) : ℝ) = ((250000000000 / 452546167821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12773_neg : (598445147 / 1000000000) ≤ -Real.log (250000000000 / 454821969019) ∧
    -Real.log (250000000000 / 454821969019) ≤ (149611287 / 250000000) := by
  have h := checkLog_sound (w := (204821969019 / 704821969019)) (n := 12)
    (lo := (598445147 / 1000000000)) (hi := (149611287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454821969019 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454821969019 / 250000000000) = 1/(250000000000 / 454821969019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12773 : Bounds (598445147 / 1000000000) (149611287 / 250000000) (Real.log (454821969019 / 250000000000)) := by
  have h := reflection_log_12773_neg
  have he : Real.log (454821969019 / 250000000000) = -Real.log (250000000000 / 454821969019) := by
    rw [show ((454821969019 / 250000000000) : ℝ) = ((250000000000 / 454821969019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12774_neg : (1222481769 / 1000000000) ≤ -Real.log (250000000000 / 848901098901) ∧
    -Real.log (250000000000 / 848901098901) ≤ (1222481771 / 1000000000) := by
  have h := checkLog_sound (w := (348901098901 / 1348901098901)) (n := 12)
    (lo := (529334589 / 1000000000)) (hi := (52933459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848901098901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(848901098901 / 500000000000) = 1/(250000000000 / 848901098901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12774 : Bounds (1222481769 / 1000000000) (1222481771 / 1000000000) (Real.log (848901098901 / 250000000000)) := by
  have h := reflection_log_12774_neg
  have he : Real.log (848901098901 / 250000000000) = -Real.log (250000000000 / 848901098901) := by
    rw [show ((848901098901 / 250000000000) : ℝ) = ((250000000000 / 848901098901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12775_neg : (1231036873 / 1000000000) ≤ -Real.log (500000000000 / 1712389380531) ∧
    -Real.log (500000000000 / 1712389380531) ≤ (1969659 / 1600000) := by
  have h := checkLog_sound (w := (712389380531 / 2712389380531)) (n := 12)
    (lo := (537889693 / 1000000000)) (hi := (268944847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1712389380531 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1712389380531 / 1000000000000) = 1/(500000000000 / 1712389380531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12775 : Bounds (1231036873 / 1000000000) (1969659 / 1600000) (Real.log (1712389380531 / 500000000000)) := by
  have h := reflection_log_12775_neg
  have he : Real.log (1712389380531 / 500000000000) = -Real.log (500000000000 / 1712389380531) := by
    rw [show ((1712389380531 / 500000000000) : ℝ) = ((500000000000 / 1712389380531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12776_neg : (109724971 / 250000000) ≤ -Real.log (1000 / 1551) ∧
    -Real.log (1000 / 1551) ≤ (87779977 / 200000000) := by
  have h := checkLog_sound (w := (551 / 2551)) (n := 12)
    (lo := (109724971 / 250000000)) (hi := (87779977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1551 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1551 / 1000) = 1/(1000 / 1551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12776 : Bounds (109724971 / 250000000) (87779977 / 200000000) (Real.log (1551 / 1000)) := by
  have h := reflection_log_12776_neg
  have he : Real.log (1551 / 1000) = -Real.log (1000 / 1551) := by
    rw [show ((1551 / 1000) : ℝ) = ((1000 / 1551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12777_neg : (80073239 / 100000000) ≤ -Real.log (449 / 1000) ∧
    -Real.log (449 / 1000) ≤ (100091549 / 125000000) := by
  have h := checkLog_sound (w := (51 / 949)) (n := 12)
    (lo := (10758521 / 100000000)) (hi := (107585211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 449) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 449) = 1/(449 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12777 : Bounds (-100091549 / 125000000) (-80073239 / 100000000) (Real.log (449 / 1000)) := by
  have h := reflection_log_12777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12778_neg : (8607 / 15625000) ≤ -Real.log (1000000 / 1000551) ∧
    -Real.log (1000000 / 1000551) ≤ (550849 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 2000551)) (n := 12)
    (lo := (8607 / 15625000)) (hi := (550849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000551 / 1000000) = 1/(1000000 / 1000551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12778 : Bounds (8607 / 15625000) (550849 / 1000000000) (Real.log (1000551 / 1000000)) := by
  have h := reflection_log_12778_neg
  have he : Real.log (1000551 / 1000000) = -Real.log (1000000 / 1000551) := by
    rw [show ((1000551 / 1000000) : ℝ) = ((1000000 / 1000551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12779_neg : (551151 / 1000000000) ≤ -Real.log (999449 / 1000000) ∧
    -Real.log (999449 / 1000000) ≤ (34447 / 62500000) := by
  have h := checkLog_sound (w := (551 / 1999449)) (n := 12)
    (lo := (551151 / 1000000000)) (hi := (34447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999449) = 1/(999449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12779 : Bounds (-34447 / 62500000) (-551151 / 1000000000) (Real.log (999449 / 1000000)) := by
  have h := reflection_log_12779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12780_neg : (254709657 / 1000000000) ≤ -Real.log (1000000 / 1290087) ∧
    -Real.log (1000000 / 1290087) ≤ (127354829 / 500000000) := by
  have h := checkLog_sound (w := (290087 / 2290087)) (n := 12)
    (lo := (254709657 / 1000000000)) (hi := (127354829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290087 / 1000000) = 1/(1000000 / 1290087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12780 : Bounds (254709657 / 1000000000) (127354829 / 500000000) (Real.log (1290087 / 1000000)) := by
  have h := reflection_log_12780_neg
  have he : Real.log (1290087 / 1000000) = -Real.log (1000000 / 1290087) := by
    rw [show ((1290087 / 1000000) : ℝ) = ((1000000 / 1290087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12781_neg : (342612851 / 1000000000) ≤ -Real.log (709913 / 1000000) ∧
    -Real.log (709913 / 1000000) ≤ (85653213 / 250000000) := by
  have h := checkLog_sound (w := (290087 / 1709913)) (n := 12)
    (lo := (342612851 / 1000000000)) (hi := (85653213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709913) = 1/(709913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12781 : Bounds (-85653213 / 250000000) (-342612851 / 1000000000) (Real.log (709913 / 1000000)) := by
  have h := reflection_log_12781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12782_neg : (64123691 / 250000000) ≤ -Real.log (125000 / 161549) ∧
    -Real.log (125000 / 161549) ≤ (51298953 / 200000000) := by
  have h := checkLog_sound (w := (36549 / 286549)) (n := 12)
    (lo := (64123691 / 250000000)) (hi := (51298953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161549 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161549 / 125000) = 1/(125000 / 161549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12782 : Bounds (64123691 / 250000000) (51298953 / 200000000) (Real.log (161549 / 125000)) := by
  have h := reflection_log_12782_neg
  have he : Real.log (161549 / 125000) = -Real.log (125000 / 161549) := by
    rw [show ((161549 / 125000) : ℝ) = ((125000 / 161549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12783_neg : (34586501 / 100000000) ≤ -Real.log (88451 / 125000) ∧
    -Real.log (88451 / 125000) ≤ (345865011 / 1000000000) := by
  have h := checkLog_sound (w := (36549 / 213451)) (n := 12)
    (lo := (34586501 / 100000000)) (hi := (345865011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88451) = 1/(88451 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12783 : Bounds (-345865011 / 1000000000) (-34586501 / 100000000) (Real.log (88451 / 125000)) := by
  have h := reflection_log_12783_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12784_neg : (44685123 / 500000000) ≤ -Real.log (14289170599 / 15625000000) ∧
    -Real.log (14289170599 / 15625000000) ≤ (89370247 / 1000000000) := by
  have h := checkLog_sound (w := (1335829401 / 29914170599)) (n := 12)
    (lo := (44685123 / 500000000)) (hi := (89370247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14289170599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14289170599) = 1/(14289170599 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12784 : Bounds (-89370247 / 1000000000) (-44685123 / 500000000) (Real.log (14289170599 / 15625000000)) := by
  have h := reflection_log_12784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12785_neg : (87903193 / 1000000000) ≤ -Real.log (915849532431 / 1000000000000) ∧
    -Real.log (915849532431 / 1000000000000) ≤ (43951597 / 500000000) := by
  have h := checkLog_sound (w := (84150467569 / 1915849532431)) (n := 12)
    (lo := (87903193 / 1000000000)) (hi := (43951597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 915849532431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 915849532431) = 1/(915849532431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12785 : Bounds (-43951597 / 500000000) (-87903193 / 1000000000) (Real.log (915849532431 / 1000000000000)) := by
  have h := reflection_log_12785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12786_neg : (597322509 / 1000000000) ≤ -Real.log (25000000000 / 45431165509) ∧
    -Real.log (25000000000 / 45431165509) ≤ (59732251 / 100000000) := by
  have h := checkLog_sound (w := (20431165509 / 70431165509)) (n := 12)
    (lo := (597322509 / 1000000000)) (hi := (59732251 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45431165509 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45431165509 / 25000000000) = 1/(25000000000 / 45431165509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12786 : Bounds (597322509 / 1000000000) (59732251 / 100000000) (Real.log (45431165509 / 25000000000)) := by
  have h := reflection_log_12786_neg
  have he : Real.log (45431165509 / 25000000000) = -Real.log (25000000000 / 45431165509) := by
    rw [show ((45431165509 / 25000000000) : ℝ) = ((25000000000 / 45431165509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12787_neg : (24094391 / 40000000) ≤ -Real.log (250000000000 / 456605917401) ∧
    -Real.log (250000000000 / 456605917401) ≤ (18823743 / 31250000) := by
  have h := checkLog_sound (w := (206605917401 / 706605917401)) (n := 12)
    (lo := (24094391 / 40000000)) (hi := (18823743 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((456605917401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(456605917401 / 250000000000) = 1/(250000000000 / 456605917401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12787 : Bounds (24094391 / 40000000) (18823743 / 31250000) (Real.log (456605917401 / 250000000000)) := by
  have h := reflection_log_12787_neg
  have he : Real.log (456605917401 / 250000000000) = -Real.log (250000000000 / 456605917401) := by
    rw [show ((456605917401 / 250000000000) : ℝ) = ((250000000000 / 456605917401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12788_neg : (1231036873 / 1000000000) ≤ -Real.log (50000000000 / 171238938053) ∧
    -Real.log (50000000000 / 171238938053) ≤ (1969659 / 1600000) := by
  have h := checkLog_sound (w := (71238938053 / 271238938053)) (n := 12)
    (lo := (537889693 / 1000000000)) (hi := (268944847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171238938053 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171238938053 / 100000000000) = 1/(50000000000 / 171238938053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12788 : Bounds (1231036873 / 1000000000) (1969659 / 1600000) (Real.log (171238938053 / 50000000000)) := by
  have h := reflection_log_12788_neg
  have he : Real.log (171238938053 / 50000000000) = -Real.log (50000000000 / 171238938053) := by
    rw [show ((171238938053 / 50000000000) : ℝ) = ((50000000000 / 171238938053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12789_neg : (619816137 / 500000000) ≤ -Real.log (100000000000 / 345434298441) ∧
    -Real.log (100000000000 / 345434298441) ≤ (309908069 / 250000000) := by
  have h := checkLog_sound (w := (145434298441 / 545434298441)) (n := 12)
    (lo := (273242547 / 500000000)) (hi := (109297019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345434298441 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(345434298441 / 200000000000) = 1/(100000000000 / 345434298441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12789 : Bounds (619816137 / 500000000) (309908069 / 250000000) (Real.log (345434298441 / 100000000000)) := by
  have h := reflection_log_12789_neg
  have he : Real.log (345434298441 / 100000000000) = -Real.log (100000000000 / 345434298441) := by
    rw [show ((345434298441 / 100000000000) : ℝ) = ((100000000000 / 345434298441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12790_neg : (440832251 / 1000000000) ≤ -Real.log (500 / 777) ∧
    -Real.log (500 / 777) ≤ (110208063 / 250000000) := by
  have h := checkLog_sound (w := (277 / 1277)) (n := 12)
    (lo := (440832251 / 1000000000)) (hi := (110208063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777 / 500) = 1/(500 / 777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12790 : Bounds (440832251 / 1000000000) (110208063 / 250000000) (Real.log (777 / 500)) := by
  have h := reflection_log_12790_neg
  have he : Real.log (777 / 500) = -Real.log (500 / 777) := by
    rw [show ((777 / 500) : ℝ) = ((500 / 777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12791_neg : (403718163 / 500000000) ≤ -Real.log (223 / 500) ∧
    -Real.log (223 / 500) ≤ (100929541 / 125000000) := by
  have h := checkLog_sound (w := (27 / 473)) (n := 12)
    (lo := (57144573 / 500000000)) (hi := (114289147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 223) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 223) = 1/(223 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12791 : Bounds (-100929541 / 125000000) (-403718163 / 500000000) (Real.log (223 / 500)) := by
  have h := reflection_log_12791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12792_neg : (276923 / 500000000) ≤ -Real.log (500000 / 500277) ∧
    -Real.log (500000 / 500277) ≤ (553847 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1000277)) (n := 12)
    (lo := (276923 / 500000000)) (hi := (553847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500277 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500277 / 500000) = 1/(500000 / 500277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12792 : Bounds (276923 / 500000000) (553847 / 1000000000) (Real.log (500277 / 500000)) := by
  have h := reflection_log_12792_neg
  have he : Real.log (500277 / 500000) = -Real.log (500000 / 500277) := by
    rw [show ((500277 / 500000) : ℝ) = ((500000 / 500277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12793_neg : (554153 / 1000000000) ≤ -Real.log (499723 / 500000) ∧
    -Real.log (499723 / 500000) ≤ (277077 / 500000000) := by
  have h := checkLog_sound (w := (277 / 999723)) (n := 12)
    (lo := (554153 / 1000000000)) (hi := (277077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499723) = 1/(499723 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12793 : Bounds (-277077 / 500000000) (-554153 / 1000000000) (Real.log (499723 / 500000)) := by
  have h := reflection_log_12793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12794_neg : (10243817 / 40000000) ≤ -Real.log (250000 / 322969) ∧
    -Real.log (250000 / 322969) ≤ (128047713 / 500000000) := by
  have h := checkLog_sound (w := (72969 / 572969)) (n := 12)
    (lo := (10243817 / 40000000)) (hi := (128047713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322969 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322969 / 250000) = 1/(250000 / 322969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12794 : Bounds (10243817 / 40000000) (128047713 / 500000000) (Real.log (322969 / 250000)) := by
  have h := reflection_log_12794_neg
  have he : Real.log (322969 / 250000) = -Real.log (250000 / 322969) := by
    rw [show ((322969 / 250000) : ℝ) = ((250000 / 322969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12795_neg : (345136059 / 1000000000) ≤ -Real.log (177031 / 250000) ∧
    -Real.log (177031 / 250000) ≤ (17256803 / 50000000) := by
  have h := checkLog_sound (w := (72969 / 427031)) (n := 12)
    (lo := (345136059 / 1000000000)) (hi := (17256803 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 177031) = 1/(177031 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12795 : Bounds (-17256803 / 50000000) (-345136059 / 1000000000) (Real.log (177031 / 250000)) := by
  have h := reflection_log_12795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12796_neg : (128940963 / 500000000) ≤ -Real.log (500000 / 647093) ∧
    -Real.log (500000 / 647093) ≤ (257881927 / 1000000000) := by
  have h := checkLog_sound (w := (147093 / 1147093)) (n := 12)
    (lo := (128940963 / 500000000)) (hi := (257881927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647093 / 500000) = 1/(500000 / 647093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12796 : Bounds (128940963 / 500000000) (257881927 / 1000000000) (Real.log (647093 / 500000)) := by
  have h := reflection_log_12796_neg
  have he : Real.log (647093 / 500000) = -Real.log (500000 / 647093) := by
    rw [show ((647093 / 500000) : ℝ) = ((500000 / 647093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12797_neg : (87100883 / 250000000) ≤ -Real.log (352907 / 500000) ∧
    -Real.log (352907 / 500000) ≤ (348403533 / 1000000000) := by
  have h := checkLog_sound (w := (147093 / 852907)) (n := 12)
    (lo := (87100883 / 250000000)) (hi := (348403533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352907) = 1/(352907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12797 : Bounds (-348403533 / 1000000000) (-87100883 / 250000000) (Real.log (352907 / 500000)) := by
  have h := reflection_log_12797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12798_neg : (45260803 / 500000000) ≤ -Real.log (228363649351 / 250000000000) ∧
    -Real.log (228363649351 / 250000000000) ≤ (90521607 / 1000000000) := by
  have h := checkLog_sound (w := (21636350649 / 478363649351)) (n := 12)
    (lo := (45260803 / 500000000)) (hi := (90521607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 228363649351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 228363649351) = 1/(228363649351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12798 : Bounds (-90521607 / 1000000000) (-45260803 / 500000000) (Real.log (228363649351 / 250000000000)) := by
  have h := reflection_log_12798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12799_neg : (89040633 / 1000000000) ≤ -Real.log (57175525039 / 62500000000) ∧
    -Real.log (57175525039 / 62500000000) ≤ (44520317 / 500000000) := by
  have h := checkLog_sound (w := (5324474961 / 119675525039)) (n := 12)
    (lo := (89040633 / 1000000000)) (hi := (44520317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 57175525039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 57175525039) = 1/(57175525039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12799 : Bounds (-44520317 / 500000000) (-89040633 / 1000000000) (Real.log (57175525039 / 62500000000)) := by
  have h := reflection_log_12799_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0200 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12800_neg : (150307871 / 250000000) ≤ -Real.log (125000000000 / 228045511803) ∧
    -Real.log (125000000000 / 228045511803) ≤ (120246297 / 200000000) := by
  have h := checkLog_sound (w := (103045511803 / 353045511803)) (n := 12)
    (lo := (150307871 / 250000000)) (hi := (120246297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228045511803 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228045511803 / 125000000000) = 1/(125000000000 / 228045511803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12800 : Bounds (150307871 / 250000000) (120246297 / 200000000) (Real.log (228045511803 / 125000000000)) := by
  have h := reflection_log_12800_neg
  have he : Real.log (228045511803 / 125000000000) = -Real.log (125000000000 / 228045511803) := by
    rw [show ((228045511803 / 125000000000) : ℝ) = ((125000000000 / 228045511803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12801_neg : (303142729 / 500000000) ≤ -Real.log (125000000000 / 229200965127) ∧
    -Real.log (125000000000 / 229200965127) ≤ (606285459 / 1000000000) := by
  have h := checkLog_sound (w := (104200965127 / 354200965127)) (n := 12)
    (lo := (303142729 / 500000000)) (hi := (606285459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229200965127 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229200965127 / 125000000000) = 1/(125000000000 / 229200965127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12801 : Bounds (303142729 / 500000000) (606285459 / 1000000000) (Real.log (229200965127 / 125000000000)) := by
  have h := reflection_log_12801_neg
  have he : Real.log (229200965127 / 125000000000) = -Real.log (125000000000 / 229200965127) := by
    rw [show ((229200965127 / 125000000000) : ℝ) = ((125000000000 / 229200965127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12802_neg : (619816137 / 500000000) ≤ -Real.log (125000000000 / 431792873051) ∧
    -Real.log (125000000000 / 431792873051) ≤ (309908069 / 250000000) := by
  have h := checkLog_sound (w := (181792873051 / 681792873051)) (n := 12)
    (lo := (273242547 / 500000000)) (hi := (109297019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431792873051 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(431792873051 / 250000000000) = 1/(125000000000 / 431792873051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12802 : Bounds (619816137 / 500000000) (309908069 / 250000000) (Real.log (431792873051 / 125000000000)) := by
  have h := reflection_log_12802_neg
  have he : Real.log (431792873051 / 125000000000) = -Real.log (125000000000 / 431792873051) := by
    rw [show ((431792873051 / 125000000000) : ℝ) = ((125000000000 / 431792873051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12803_neg : (624134289 / 500000000) ≤ -Real.log (7812500000 / 27221132287) ∧
    -Real.log (7812500000 / 27221132287) ≤ (62413429 / 50000000) := by
  have h := checkLog_sound (w := (11596132287 / 42846132287)) (n := 12)
    (lo := (277560699 / 500000000)) (hi := (555121399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27221132287 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(27221132287 / 15625000000) = 1/(7812500000 / 27221132287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12803 : Bounds (624134289 / 500000000) (62413429 / 50000000) (Real.log (27221132287 / 7812500000)) := by
  have h := reflection_log_12803_neg
  have he : Real.log (27221132287 / 7812500000) = -Real.log (7812500000 / 27221132287) := by
    rw [show ((27221132287 / 7812500000) : ℝ) = ((7812500000 / 27221132287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12804_neg : (110690223 / 250000000) ≤ -Real.log (1000 / 1557) ∧
    -Real.log (1000 / 1557) ≤ (442760893 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 2557)) (n := 12)
    (lo := (110690223 / 250000000)) (hi := (442760893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557 / 1000) = 1/(1000 / 1557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12804 : Bounds (110690223 / 250000000) (442760893 / 1000000000) (Real.log (1557 / 1000)) := by
  have h := reflection_log_12804_neg
  have he : Real.log (1557 / 1000) = -Real.log (1000 / 1557) := by
    rw [show ((1557 / 1000) : ℝ) = ((1000 / 1557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12805_neg : (203546377 / 250000000) ≤ -Real.log (443 / 1000) ∧
    -Real.log (443 / 1000) ≤ (81418551 / 100000000) := by
  have h := checkLog_sound (w := (57 / 943)) (n := 12)
    (lo := (15129791 / 125000000)) (hi := (121038329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 443) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 443) = 1/(443 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12805 : Bounds (-81418551 / 100000000) (-203546377 / 250000000) (Real.log (443 / 1000)) := by
  have h := reflection_log_12805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12806_neg : (139211 / 250000000) ≤ -Real.log (1000000 / 1000557) ∧
    -Real.log (1000000 / 1000557) ≤ (111369 / 200000000) := by
  have h := checkLog_sound (w := (557 / 2000557)) (n := 12)
    (lo := (139211 / 250000000)) (hi := (111369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000557 / 1000000) = 1/(1000000 / 1000557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12806 : Bounds (139211 / 250000000) (111369 / 200000000) (Real.log (1000557 / 1000000)) := by
  have h := reflection_log_12806_neg
  have he : Real.log (1000557 / 1000000) = -Real.log (1000000 / 1000557) := by
    rw [show ((1000557 / 1000000) : ℝ) = ((1000000 / 1000557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12807_neg : (111431 / 200000000) ≤ -Real.log (999443 / 1000000) ∧
    -Real.log (999443 / 1000000) ≤ (139289 / 250000000) := by
  have h := checkLog_sound (w := (557 / 1999443)) (n := 12)
    (lo := (111431 / 200000000)) (hi := (139289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999443) = 1/(999443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12807 : Bounds (-139289 / 250000000) (-111431 / 200000000) (Real.log (999443 / 1000000)) := by
  have h := reflection_log_12807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12808_neg : (128740797 / 500000000) ≤ -Real.log (250000 / 323417) ∧
    -Real.log (250000 / 323417) ≤ (51496319 / 200000000) := by
  have h := checkLog_sound (w := (73417 / 573417)) (n := 12)
    (lo := (128740797 / 500000000)) (hi := (51496319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323417 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323417 / 250000) = 1/(250000 / 323417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12808 : Bounds (128740797 / 500000000) (51496319 / 200000000) (Real.log (323417 / 250000)) := by
  have h := reflection_log_12808_neg
  have he : Real.log (323417 / 250000) = -Real.log (250000 / 323417) := by
    rw [show ((323417 / 250000) : ℝ) = ((250000 / 323417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12809_neg : (347669897 / 1000000000) ≤ -Real.log (176583 / 250000) ∧
    -Real.log (176583 / 250000) ≤ (173834949 / 500000000) := by
  have h := checkLog_sound (w := (73417 / 426583)) (n := 12)
    (lo := (347669897 / 1000000000)) (hi := (173834949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 176583) = 1/(176583 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12809 : Bounds (-173834949 / 500000000) (-347669897 / 1000000000) (Real.log (176583 / 250000)) := by
  have h := reflection_log_12809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12810_neg : (64817563 / 250000000) ≤ -Real.log (62500 / 80999) ∧
    -Real.log (62500 / 80999) ≤ (259270253 / 1000000000) := by
  have h := checkLog_sound (w := (18499 / 143499)) (n := 12)
    (lo := (64817563 / 250000000)) (hi := (259270253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80999 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80999 / 62500) = 1/(62500 / 80999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12810 : Bounds (64817563 / 250000000) (259270253 / 1000000000) (Real.log (80999 / 62500)) := by
  have h := reflection_log_12810_neg
  have he : Real.log (80999 / 62500) = -Real.log (62500 / 80999) := by
    rw [show ((80999 / 62500) : ℝ) = ((62500 / 80999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12811_neg : (70190839 / 200000000) ≤ -Real.log (44001 / 62500) ∧
    -Real.log (44001 / 62500) ≤ (87738549 / 250000000) := by
  have h := checkLog_sound (w := (18499 / 106501)) (n := 12)
    (lo := (70190839 / 200000000)) (hi := (87738549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44001) = 1/(44001 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12811 : Bounds (-87738549 / 250000000) (-70190839 / 200000000) (Real.log (44001 / 62500)) := by
  have h := reflection_log_12811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12812_neg : (91683943 / 1000000000) ≤ -Real.log (3564036999 / 3906250000) ∧
    -Real.log (3564036999 / 3906250000) ≤ (11460493 / 125000000) := by
  have h := checkLog_sound (w := (342213001 / 7470286999)) (n := 12)
    (lo := (91683943 / 1000000000)) (hi := (11460493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3564036999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3564036999) = 1/(3564036999 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12812 : Bounds (-11460493 / 125000000) (-91683943 / 1000000000) (Real.log (3564036999 / 3906250000)) := by
  have h := reflection_log_12812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12813_neg : (45094151 / 500000000) ≤ -Real.log (57109944111 / 62500000000) ∧
    -Real.log (57109944111 / 62500000000) ≤ (90188303 / 1000000000) := by
  have h := checkLog_sound (w := (5390055889 / 119609944111)) (n := 12)
    (lo := (45094151 / 500000000)) (hi := (90188303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 57109944111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 57109944111) = 1/(57109944111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12813 : Bounds (-90188303 / 1000000000) (-45094151 / 500000000) (Real.log (57109944111 / 62500000000)) := by
  have h := reflection_log_12813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12814_neg : (605151491 / 1000000000) ≤ -Real.log (500000000000 / 915764824473) ∧
    -Real.log (500000000000 / 915764824473) ≤ (151287873 / 250000000) := by
  have h := checkLog_sound (w := (415764824473 / 1415764824473)) (n := 12)
    (lo := (605151491 / 1000000000)) (hi := (151287873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915764824473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915764824473 / 500000000000) = 1/(500000000000 / 915764824473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12814 : Bounds (605151491 / 1000000000) (151287873 / 250000000) (Real.log (915764824473 / 500000000000)) := by
  have h := reflection_log_12814_neg
  have he : Real.log (915764824473 / 500000000000) = -Real.log (500000000000 / 915764824473) := by
    rw [show ((915764824473 / 500000000000) : ℝ) = ((500000000000 / 915764824473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12815_neg : (610224447 / 1000000000) ≤ -Real.log (500000000000 / 920422263131) ∧
    -Real.log (500000000000 / 920422263131) ≤ (9534757 / 15625000) := by
  have h := checkLog_sound (w := (420422263131 / 1420422263131)) (n := 12)
    (lo := (610224447 / 1000000000)) (hi := (9534757 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920422263131 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(920422263131 / 500000000000) = 1/(500000000000 / 920422263131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12815 : Bounds (610224447 / 1000000000) (9534757 / 15625000) (Real.log (920422263131 / 500000000000)) := by
  have h := reflection_log_12815_neg
  have he : Real.log (920422263131 / 500000000000) = -Real.log (500000000000 / 920422263131) := by
    rw [show ((920422263131 / 500000000000) : ℝ) = ((500000000000 / 920422263131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12816_neg : (624134289 / 500000000) ≤ -Real.log (500000000000 / 1742152466367) ∧
    -Real.log (500000000000 / 1742152466367) ≤ (62413429 / 50000000) := by
  have h := checkLog_sound (w := (742152466367 / 2742152466367)) (n := 12)
    (lo := (277560699 / 500000000)) (hi := (555121399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1742152466367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1742152466367 / 1000000000000) = 1/(500000000000 / 1742152466367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12816 : Bounds (624134289 / 500000000) (62413429 / 50000000) (Real.log (1742152466367 / 500000000000)) := by
  have h := reflection_log_12816_neg
  have he : Real.log (1742152466367 / 500000000000) = -Real.log (500000000000 / 1742152466367) := by
    rw [show ((1742152466367 / 500000000000) : ℝ) = ((500000000000 / 1742152466367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12817_neg : (1256946401 / 1000000000) ≤ -Real.log (125000000000 / 439334085779) ∧
    -Real.log (125000000000 / 439334085779) ≤ (1256946403 / 1000000000) := by
  have h := checkLog_sound (w := (189334085779 / 689334085779)) (n := 12)
    (lo := (563799221 / 1000000000)) (hi := (281899611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439334085779 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(439334085779 / 250000000000) = 1/(125000000000 / 439334085779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12817 : Bounds (1256946401 / 1000000000) (1256946403 / 1000000000) (Real.log (439334085779 / 125000000000)) := by
  have h := reflection_log_12817_neg
  have he : Real.log (439334085779 / 125000000000) = -Real.log (125000000000 / 439334085779) := by
    rw [show ((439334085779 / 125000000000) : ℝ) = ((125000000000 / 439334085779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12818_neg : (444685821 / 1000000000) ≤ -Real.log (25 / 39) ∧
    -Real.log (25 / 39) ≤ (222342911 / 500000000) := by
  have h := checkLog_sound (w := (7 / 32)) (n := 12)
    (lo := (444685821 / 1000000000)) (hi := (222342911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39 / 25) = 1/(25 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12818 : Bounds (444685821 / 1000000000) (222342911 / 500000000) (Real.log (39 / 25)) := by
  have h := reflection_log_12818_neg
  have he : Real.log (39 / 25) = -Real.log (25 / 39) := by
    rw [show ((39 / 25) : ℝ) = ((25 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12819_neg : (820980551 / 1000000000) ≤ -Real.log (11 / 25) ∧
    -Real.log (11 / 25) ≤ (820980553 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 47)) (n := 12)
    (lo := (127833371 / 1000000000)) (hi := (31958343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 22) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 22) = 1/(11 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12819 : Bounds (-820980553 / 1000000000) (-820980551 / 1000000000) (Real.log (11 / 25)) := by
  have h := reflection_log_12819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12820_neg : (559843 / 1000000000) ≤ -Real.log (12500 / 12507) ∧
    -Real.log (12500 / 12507) ≤ (139961 / 250000000) := by
  have h := checkLog_sound (w := (7 / 25007)) (n := 12)
    (lo := (559843 / 1000000000)) (hi := (139961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12507 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12507 / 12500) = 1/(12500 / 12507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12820 : Bounds (559843 / 1000000000) (139961 / 250000000) (Real.log (12507 / 12500)) := by
  have h := reflection_log_12820_neg
  have he : Real.log (12507 / 12500) = -Real.log (12500 / 12507) := by
    rw [show ((12507 / 12500) : ℝ) = ((12500 / 12507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12821_neg : (140039 / 250000000) ≤ -Real.log (12493 / 12500) ∧
    -Real.log (12493 / 12500) ≤ (560157 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 24993)) (n := 12)
    (lo := (140039 / 250000000)) (hi := (560157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 12493) = 1/(12493 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12821 : Bounds (-560157 / 1000000000) (-140039 / 250000000) (Real.log (12493 / 12500)) := by
  have h := reflection_log_12821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12822_neg : (64717233 / 250000000) ≤ -Real.log (125000 / 161933) ∧
    -Real.log (125000 / 161933) ≤ (258868933 / 1000000000) := by
  have h := checkLog_sound (w := (36933 / 286933)) (n := 12)
    (lo := (64717233 / 250000000)) (hi := (258868933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161933 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161933 / 125000) = 1/(125000 / 161933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12822 : Bounds (64717233 / 250000000) (258868933 / 1000000000) (Real.log (161933 / 125000)) := by
  have h := reflection_log_12822_neg
  have he : Real.log (161933 / 125000) = -Real.log (125000 / 161933) := by
    rw [show ((161933 / 125000) : ℝ) = ((125000 / 161933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12823_neg : (43776981 / 125000000) ≤ -Real.log (88067 / 125000) ∧
    -Real.log (88067 / 125000) ≤ (350215849 / 1000000000) := by
  have h := checkLog_sound (w := (36933 / 213067)) (n := 12)
    (lo := (43776981 / 125000000)) (hi := (350215849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88067) = 1/(88067 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12823 : Bounds (-350215849 / 1000000000) (-43776981 / 125000000) (Real.log (88067 / 125000)) := by
  have h := reflection_log_12823_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12824_neg : (130330253 / 500000000) ≤ -Real.log (1000000 / 1297787) ∧
    -Real.log (1000000 / 1297787) ≤ (260660507 / 1000000000) := by
  have h := checkLog_sound (w := (297787 / 2297787)) (n := 12)
    (lo := (130330253 / 500000000)) (hi := (260660507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297787 / 1000000) = 1/(1000000 / 1297787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12824 : Bounds (130330253 / 500000000) (260660507 / 1000000000) (Real.log (1297787 / 1000000)) := by
  have h := reflection_log_12824_neg
  have he : Real.log (1297787 / 1000000) = -Real.log (1000000 / 1297787) := by
    rw [show ((1297787 / 1000000) : ℝ) = ((1000000 / 1297787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12825_neg : (176759251 / 500000000) ≤ -Real.log (702213 / 1000000) ∧
    -Real.log (702213 / 1000000) ≤ (353518503 / 1000000000) := by
  have h := checkLog_sound (w := (297787 / 1702213)) (n := 12)
    (lo := (176759251 / 500000000)) (hi := (353518503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702213) = 1/(702213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12825 : Bounds (-353518503 / 1000000000) (-176759251 / 500000000) (Real.log (702213 / 1000000)) := by
  have h := reflection_log_12825_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12826_neg : (18571599 / 200000000) ≤ -Real.log (911322902631 / 1000000000000) ∧
    -Real.log (911322902631 / 1000000000000) ≤ (23214499 / 250000000) := by
  have h := checkLog_sound (w := (88677097369 / 1911322902631)) (n := 12)
    (lo := (18571599 / 200000000)) (hi := (23214499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 911322902631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 911322902631) = 1/(911322902631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12826 : Bounds (-23214499 / 250000000) (-18571599 / 200000000) (Real.log (911322902631 / 1000000000000)) := by
  have h := reflection_log_12826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12827_neg : (22836729 / 250000000) ≤ -Real.log (14260953511 / 15625000000) ∧
    -Real.log (14260953511 / 15625000000) ≤ (91346917 / 1000000000) := by
  have h := checkLog_sound (w := (1364046489 / 29885953511)) (n := 12)
    (lo := (22836729 / 250000000)) (hi := (91346917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14260953511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14260953511) = 1/(14260953511 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12827 : Bounds (-91346917 / 1000000000) (-22836729 / 250000000) (Real.log (14260953511 / 15625000000)) := by
  have h := reflection_log_12827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12828_neg : (609084781 / 1000000000) ≤ -Real.log (500000000000 / 919373885791) ∧
    -Real.log (500000000000 / 919373885791) ≤ (304542391 / 500000000) := by
  have h := checkLog_sound (w := (419373885791 / 1419373885791)) (n := 12)
    (lo := (609084781 / 1000000000)) (hi := (304542391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919373885791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919373885791 / 500000000000) = 1/(500000000000 / 919373885791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12828 : Bounds (609084781 / 1000000000) (304542391 / 500000000) (Real.log (919373885791 / 500000000000)) := by
  have h := reflection_log_12828_neg
  have he : Real.log (919373885791 / 500000000000) = -Real.log (500000000000 / 919373885791) := by
    rw [show ((919373885791 / 500000000000) : ℝ) = ((500000000000 / 919373885791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12829_neg : (9596547 / 15625000) ≤ -Real.log (31250000000 / 57754333443) ∧
    -Real.log (31250000000 / 57754333443) ≤ (614179009 / 1000000000) := by
  have h := checkLog_sound (w := (26504333443 / 89004333443)) (n := 12)
    (lo := (9596547 / 15625000)) (hi := (614179009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57754333443 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57754333443 / 31250000000) = 1/(31250000000 / 57754333443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12829 : Bounds (9596547 / 15625000) (614179009 / 1000000000) (Real.log (57754333443 / 31250000000)) := by
  have h := reflection_log_12829_neg
  have he : Real.log (57754333443 / 31250000000) = -Real.log (31250000000 / 57754333443) := by
    rw [show ((57754333443 / 31250000000) : ℝ) = ((31250000000 / 57754333443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12830_neg : (1256946401 / 1000000000) ≤ -Real.log (100000000000 / 351467268623) ∧
    -Real.log (100000000000 / 351467268623) ≤ (1256946403 / 1000000000) := by
  have h := checkLog_sound (w := (151467268623 / 551467268623)) (n := 12)
    (lo := (563799221 / 1000000000)) (hi := (281899611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351467268623 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(351467268623 / 200000000000) = 1/(100000000000 / 351467268623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12830 : Bounds (1256946401 / 1000000000) (1256946403 / 1000000000) (Real.log (351467268623 / 100000000000)) := by
  have h := reflection_log_12830_neg
  have he : Real.log (351467268623 / 100000000000) = -Real.log (100000000000 / 351467268623) := by
    rw [show ((351467268623 / 100000000000) : ℝ) = ((100000000000 / 351467268623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12831_neg : (316416593 / 250000000) ≤ -Real.log (62500000000 / 221590909091) ∧
    -Real.log (62500000000 / 221590909091) ≤ (632833187 / 500000000) := by
  have h := checkLog_sound (w := (96590909091 / 346590909091)) (n := 12)
    (lo := (71564899 / 125000000)) (hi := (572519193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221590909091 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(221590909091 / 125000000000) = 1/(62500000000 / 221590909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12831 : Bounds (316416593 / 250000000) (632833187 / 500000000) (Real.log (221590909091 / 62500000000)) := by
  have h := reflection_log_12831_neg
  have he : Real.log (221590909091 / 62500000000) = -Real.log (62500000000 / 221590909091) := by
    rw [show ((221590909091 / 62500000000) : ℝ) = ((62500000000 / 221590909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12832_neg : (446607051 / 1000000000) ≤ -Real.log (1000 / 1563) ∧
    -Real.log (1000 / 1563) ≤ (111651763 / 250000000) := by
  have h := checkLog_sound (w := (563 / 2563)) (n := 12)
    (lo := (446607051 / 1000000000)) (hi := (111651763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563 / 1000) = 1/(1000 / 1563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12832 : Bounds (446607051 / 1000000000) (111651763 / 250000000) (Real.log (1563 / 1000)) := by
  have h := reflection_log_12832_neg
  have he : Real.log (1563 / 1000) = -Real.log (1000 / 1563) := by
    rw [show ((1563 / 1000) : ℝ) = ((1000 / 1563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12833_neg : (827822083 / 1000000000) ≤ -Real.log (437 / 1000) ∧
    -Real.log (437 / 1000) ≤ (165564417 / 200000000) := by
  have h := checkLog_sound (w := (63 / 937)) (n := 12)
    (lo := (134674903 / 1000000000)) (hi := (16834363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 437) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 437) = 1/(437 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12833 : Bounds (-165564417 / 200000000) (-827822083 / 1000000000) (Real.log (437 / 1000)) := by
  have h := reflection_log_12833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12834_neg : (562841 / 1000000000) ≤ -Real.log (1000000 / 1000563) ∧
    -Real.log (1000000 / 1000563) ≤ (281421 / 500000000) := by
  have h := checkLog_sound (w := (563 / 2000563)) (n := 12)
    (lo := (562841 / 1000000000)) (hi := (281421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000563 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000563 / 1000000) = 1/(1000000 / 1000563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12834 : Bounds (562841 / 1000000000) (281421 / 500000000) (Real.log (1000563 / 1000000)) := by
  have h := reflection_log_12834_neg
  have he : Real.log (1000563 / 1000000) = -Real.log (1000000 / 1000563) := by
    rw [show ((1000563 / 1000000) : ℝ) = ((1000000 / 1000563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12835_neg : (281579 / 500000000) ≤ -Real.log (999437 / 1000000) ∧
    -Real.log (999437 / 1000000) ≤ (563159 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1999437)) (n := 12)
    (lo := (281579 / 500000000)) (hi := (563159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999437) = 1/(999437 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12835 : Bounds (-563159 / 1000000000) (-281579 / 500000000) (Real.log (999437 / 1000000)) := by
  have h := reflection_log_12835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12836_neg : (260257431 / 1000000000) ≤ -Real.log (62500 / 81079) ∧
    -Real.log (62500 / 81079) ≤ (32532179 / 125000000) := by
  have h := checkLog_sound (w := (18579 / 143579)) (n := 12)
    (lo := (260257431 / 1000000000)) (hi := (32532179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81079 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81079 / 62500) = 1/(62500 / 81079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12836 : Bounds (260257431 / 1000000000) (32532179 / 125000000) (Real.log (81079 / 62500)) := by
  have h := reflection_log_12836_neg
  have he : Real.log (81079 / 62500) = -Real.log (62500 / 81079) := by
    rw [show ((81079 / 62500) : ℝ) = ((62500 / 81079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12837_neg : (352773991 / 1000000000) ≤ -Real.log (43921 / 62500) ∧
    -Real.log (43921 / 62500) ≤ (44096749 / 125000000) := by
  have h := checkLog_sound (w := (18579 / 106421)) (n := 12)
    (lo := (352773991 / 1000000000)) (hi := (44096749 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43921) = 1/(43921 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12837 : Bounds (-44096749 / 125000000) (-352773991 / 1000000000) (Real.log (43921 / 62500)) := by
  have h := reflection_log_12837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12838_neg : (131025569 / 500000000) ≤ -Real.log (1000000 / 1299593) ∧
    -Real.log (1000000 / 1299593) ≤ (262051139 / 1000000000) := by
  have h := checkLog_sound (w := (299593 / 2299593)) (n := 12)
    (lo := (131025569 / 500000000)) (hi := (262051139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299593 / 1000000) = 1/(1000000 / 1299593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12838 : Bounds (131025569 / 500000000) (262051139 / 1000000000) (Real.log (1299593 / 1000000)) := by
  have h := reflection_log_12838_neg
  have he : Real.log (1299593 / 1000000) = -Real.log (1000000 / 1299593) := by
    rw [show ((1299593 / 1000000) : ℝ) = ((1000000 / 1299593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12839_neg : (89023421 / 250000000) ≤ -Real.log (700407 / 1000000) ∧
    -Real.log (700407 / 1000000) ≤ (71218737 / 200000000) := by
  have h := checkLog_sound (w := (299593 / 1700407)) (n := 12)
    (lo := (89023421 / 250000000)) (hi := (71218737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700407) = 1/(700407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12839 : Bounds (-71218737 / 200000000) (-89023421 / 250000000) (Real.log (700407 / 1000000)) := by
  have h := reflection_log_12839_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12840_neg : (18808509 / 200000000) ≤ -Real.log (910244034351 / 1000000000000) ∧
    -Real.log (910244034351 / 1000000000000) ≤ (47021273 / 500000000) := by
  have h := checkLog_sound (w := (89755965649 / 1910244034351)) (n := 12)
    (lo := (18808509 / 200000000)) (hi := (47021273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 910244034351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 910244034351) = 1/(910244034351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12840 : Bounds (-47021273 / 500000000) (-18808509 / 200000000) (Real.log (910244034351 / 1000000000000)) := by
  have h := reflection_log_12840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12841_neg : (92516559 / 1000000000) ≤ -Real.log (3561070759 / 3906250000) ∧
    -Real.log (3561070759 / 3906250000) ≤ (1156457 / 12500000) := by
  have h := checkLog_sound (w := (345179241 / 7467320759)) (n := 12)
    (lo := (92516559 / 1000000000)) (hi := (1156457 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3561070759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3561070759) = 1/(3561070759 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12841 : Bounds (-1156457 / 12500000) (-92516559 / 1000000000) (Real.log (3561070759 / 3906250000)) := by
  have h := reflection_log_12841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12842_neg : (306515711 / 500000000) ≤ -Real.log (500000000000 / 923009494319) ∧
    -Real.log (500000000000 / 923009494319) ≤ (613031423 / 1000000000) := by
  have h := checkLog_sound (w := (423009494319 / 1423009494319)) (n := 12)
    (lo := (306515711 / 500000000)) (hi := (613031423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923009494319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923009494319 / 500000000000) = 1/(500000000000 / 923009494319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12842 : Bounds (306515711 / 500000000) (613031423 / 1000000000) (Real.log (923009494319 / 500000000000)) := by
  have h := reflection_log_12842_neg
  have he : Real.log (923009494319 / 500000000000) = -Real.log (500000000000 / 923009494319) := by
    rw [show ((923009494319 / 500000000000) : ℝ) = ((500000000000 / 923009494319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12843_neg : (309072411 / 500000000) ≤ -Real.log (125000000000 / 231935324747) ∧
    -Real.log (125000000000 / 231935324747) ≤ (618144823 / 1000000000) := by
  have h := checkLog_sound (w := (106935324747 / 356935324747)) (n := 12)
    (lo := (309072411 / 500000000)) (hi := (618144823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231935324747 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231935324747 / 125000000000) = 1/(125000000000 / 231935324747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12843 : Bounds (309072411 / 500000000) (618144823 / 1000000000) (Real.log (231935324747 / 125000000000)) := by
  have h := reflection_log_12843_neg
  have he : Real.log (231935324747 / 125000000000) = -Real.log (125000000000 / 231935324747) := by
    rw [show ((231935324747 / 125000000000) : ℝ) = ((125000000000 / 231935324747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12844_neg : (316416593 / 250000000) ≤ -Real.log (500000000000 / 1772727272727) ∧
    -Real.log (500000000000 / 1772727272727) ≤ (632833187 / 500000000) := by
  have h := checkLog_sound (w := (772727272727 / 2772727272727)) (n := 12)
    (lo := (71564899 / 125000000)) (hi := (572519193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1772727272727 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1772727272727 / 1000000000000) = 1/(500000000000 / 1772727272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12844 : Bounds (316416593 / 250000000) (632833187 / 500000000) (Real.log (1772727272727 / 500000000000)) := by
  have h := reflection_log_12844_neg
  have he : Real.log (1772727272727 / 500000000000) = -Real.log (500000000000 / 1772727272727) := by
    rw [show ((1772727272727 / 500000000000) : ℝ) = ((500000000000 / 1772727272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12845_neg : (637214567 / 500000000) ≤ -Real.log (500000000000 / 1788329519451) ∧
    -Real.log (500000000000 / 1788329519451) ≤ (79651821 / 62500000) := by
  have h := checkLog_sound (w := (788329519451 / 2788329519451)) (n := 12)
    (lo := (290640977 / 500000000)) (hi := (116256391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1788329519451 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1788329519451 / 1000000000000) = 1/(500000000000 / 1788329519451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12845 : Bounds (637214567 / 500000000) (79651821 / 62500000) (Real.log (1788329519451 / 500000000000)) := by
  have h := reflection_log_12845_neg
  have he : Real.log (1788329519451 / 500000000000) = -Real.log (500000000000 / 1788329519451) := by
    rw [show ((1788329519451 / 500000000000) : ℝ) = ((500000000000 / 1788329519451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12846_neg : (448524597 / 1000000000) ≤ -Real.log (500 / 783) ∧
    -Real.log (500 / 783) ≤ (224262299 / 500000000) := by
  have h := checkLog_sound (w := (283 / 1283)) (n := 12)
    (lo := (448524597 / 1000000000)) (hi := (224262299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783 / 500) = 1/(500 / 783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12846 : Bounds (448524597 / 1000000000) (224262299 / 500000000) (Real.log (783 / 500)) := by
  have h := reflection_log_12846_neg
  have he : Real.log (783 / 500) = -Real.log (500 / 783) := by
    rw [show ((783 / 500) : ℝ) = ((500 / 783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12847_neg : (104338843 / 125000000) ≤ -Real.log (217 / 500) ∧
    -Real.log (217 / 500) ≤ (417355373 / 500000000) := by
  have h := checkLog_sound (w := (33 / 467)) (n := 12)
    (lo := (35390891 / 250000000)) (hi := (28312713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 217) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 217) = 1/(217 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12847 : Bounds (-417355373 / 500000000) (-104338843 / 125000000) (Real.log (217 / 500)) := by
  have h := reflection_log_12847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12848_neg : (565839 / 1000000000) ≤ -Real.log (500000 / 500283) ∧
    -Real.log (500000 / 500283) ≤ (7073 / 12500000) := by
  have h := checkLog_sound (w := (283 / 1000283)) (n := 12)
    (lo := (565839 / 1000000000)) (hi := (7073 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500283 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500283 / 500000) = 1/(500000 / 500283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12848 : Bounds (565839 / 1000000000) (7073 / 12500000) (Real.log (500283 / 500000)) := by
  have h := reflection_log_12848_neg
  have he : Real.log (500283 / 500000) = -Real.log (500000 / 500283) := by
    rw [show ((500283 / 500000) : ℝ) = ((500000 / 500283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12849_neg : (7077 / 12500000) ≤ -Real.log (499717 / 500000) ∧
    -Real.log (499717 / 500000) ≤ (566161 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 999717)) (n := 12)
    (lo := (7077 / 12500000)) (hi := (566161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499717) = 1/(499717 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12849 : Bounds (-566161 / 1000000000) (-7077 / 12500000) (Real.log (499717 / 500000)) := by
  have h := reflection_log_12849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12850_neg : (65411771 / 250000000) ≤ -Real.log (250000 / 324767) ∧
    -Real.log (250000 / 324767) ≤ (52329417 / 200000000) := by
  have h := checkLog_sound (w := (74767 / 574767)) (n := 12)
    (lo := (65411771 / 250000000)) (hi := (52329417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324767 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324767 / 250000) = 1/(250000 / 324767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12850 : Bounds (65411771 / 250000000) (52329417 / 200000000) (Real.log (324767 / 250000)) := by
  have h := reflection_log_12850_neg
  have he : Real.log (324767 / 250000) = -Real.log (250000 / 324767) := by
    rw [show ((324767 / 250000) : ℝ) = ((250000 / 324767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12851_neg : (888361 / 2500000) ≤ -Real.log (175233 / 250000) ∧
    -Real.log (175233 / 250000) ≤ (355344401 / 1000000000) := by
  have h := checkLog_sound (w := (74767 / 425233)) (n := 12)
    (lo := (888361 / 2500000)) (hi := (355344401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175233) = 1/(175233 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12851 : Bounds (-355344401 / 1000000000) (-888361 / 2500000) (Real.log (175233 / 250000)) := by
  have h := reflection_log_12851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12852_neg : (263442913 / 1000000000) ≤ -Real.log (1000000 / 1301403) ∧
    -Real.log (1000000 / 1301403) ≤ (131721457 / 500000000) := by
  have h := checkLog_sound (w := (301403 / 2301403)) (n := 12)
    (lo := (263442913 / 1000000000)) (hi := (131721457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301403 / 1000000) = 1/(1000000 / 1301403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12852 : Bounds (263442913 / 1000000000) (131721457 / 500000000) (Real.log (1301403 / 1000000)) := by
  have h := reflection_log_12852_neg
  have he : Real.log (1301403 / 1000000) = -Real.log (1000000 / 1301403) := by
    rw [show ((1301403 / 1000000) : ℝ) = ((1000000 / 1301403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12853_neg : (8967031 / 25000000) ≤ -Real.log (698597 / 1000000) ∧
    -Real.log (698597 / 1000000) ≤ (358681241 / 1000000000) := by
  have h := checkLog_sound (w := (301403 / 1698597)) (n := 12)
    (lo := (8967031 / 25000000)) (hi := (358681241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 698597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 698597) = 1/(698597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12853 : Bounds (-358681241 / 1000000000) (-8967031 / 25000000) (Real.log (698597 / 1000000)) := by
  have h := reflection_log_12853_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12854_neg : (95238327 / 1000000000) ≤ -Real.log (909156231591 / 1000000000000) ∧
    -Real.log (909156231591 / 1000000000000) ≤ (11904791 / 125000000) := by
  have h := checkLog_sound (w := (90843768409 / 1909156231591)) (n := 12)
    (lo := (95238327 / 1000000000)) (hi := (11904791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 909156231591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 909156231591) = 1/(909156231591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12854 : Bounds (-11904791 / 125000000) (-95238327 / 1000000000) (Real.log (909156231591 / 1000000000000)) := by
  have h := reflection_log_12854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12855_neg : (23424329 / 250000000) ≤ -Real.log (56909895711 / 62500000000) ∧
    -Real.log (56909895711 / 62500000000) ≤ (93697317 / 1000000000) := by
  have h := checkLog_sound (w := (5590104289 / 119409895711)) (n := 12)
    (lo := (23424329 / 250000000)) (hi := (93697317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56909895711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56909895711) = 1/(56909895711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12855 : Bounds (-93697317 / 1000000000) (-23424329 / 250000000) (Real.log (56909895711 / 62500000000)) := by
  have h := reflection_log_12855_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12856_neg : (123398297 / 200000000) ≤ -Real.log (500000000000 / 926671916819) ∧
    -Real.log (500000000000 / 926671916819) ≤ (308495743 / 500000000) := by
  have h := checkLog_sound (w := (426671916819 / 1426671916819)) (n := 12)
    (lo := (123398297 / 200000000)) (hi := (308495743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((926671916819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(926671916819 / 500000000000) = 1/(500000000000 / 926671916819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12856 : Bounds (123398297 / 200000000) (308495743 / 500000000) (Real.log (926671916819 / 500000000000)) := by
  have h := reflection_log_12856_neg
  have he : Real.log (926671916819 / 500000000000) = -Real.log (500000000000 / 926671916819) := by
    rw [show ((926671916819 / 500000000000) : ℝ) = ((500000000000 / 926671916819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12857_neg : (311062077 / 500000000) ≤ -Real.log (100000000000 / 186288088841) ∧
    -Real.log (100000000000 / 186288088841) ≤ (124424831 / 200000000) := by
  have h := checkLog_sound (w := (86288088841 / 286288088841)) (n := 12)
    (lo := (311062077 / 500000000)) (hi := (124424831 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186288088841 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186288088841 / 100000000000) = 1/(100000000000 / 186288088841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12857 : Bounds (311062077 / 500000000) (124424831 / 200000000) (Real.log (186288088841 / 100000000000)) := by
  have h := reflection_log_12857_neg
  have he : Real.log (186288088841 / 100000000000) = -Real.log (100000000000 / 186288088841) := by
    rw [show ((186288088841 / 100000000000) : ℝ) = ((100000000000 / 186288088841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12858_neg : (637214567 / 500000000) ≤ -Real.log (10000000000 / 35766590389) ∧
    -Real.log (10000000000 / 35766590389) ≤ (79651821 / 62500000) := by
  have h := checkLog_sound (w := (15766590389 / 55766590389)) (n := 12)
    (lo := (290640977 / 500000000)) (hi := (116256391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35766590389 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(35766590389 / 20000000000) = 1/(10000000000 / 35766590389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12858 : Bounds (637214567 / 500000000) (79651821 / 62500000) (Real.log (35766590389 / 10000000000)) := by
  have h := reflection_log_12858_neg
  have he : Real.log (35766590389 / 10000000000) = -Real.log (10000000000 / 35766590389) := by
    rw [show ((35766590389 / 10000000000) : ℝ) = ((10000000000 / 35766590389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12859_neg : (1283235341 / 1000000000) ≤ -Real.log (250000000000 / 902073732719) ∧
    -Real.log (250000000000 / 902073732719) ≤ (1283235343 / 1000000000) := by
  have h := checkLog_sound (w := (402073732719 / 1402073732719)) (n := 12)
    (lo := (590088161 / 1000000000)) (hi := (295044081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902073732719 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(902073732719 / 500000000000) = 1/(250000000000 / 902073732719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12859 : Bounds (1283235341 / 1000000000) (1283235343 / 1000000000) (Real.log (902073732719 / 250000000000)) := by
  have h := reflection_log_12859_neg
  have he : Real.log (902073732719 / 250000000000) = -Real.log (250000000000 / 902073732719) := by
    rw [show ((902073732719 / 250000000000) : ℝ) = ((250000000000 / 902073732719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12860_neg : (450438473 / 1000000000) ≤ -Real.log (1000 / 1569) ∧
    -Real.log (1000 / 1569) ≤ (225219237 / 500000000) := by
  have h := checkLog_sound (w := (569 / 2569)) (n := 12)
    (lo := (450438473 / 1000000000)) (hi := (225219237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569 / 1000) = 1/(1000 / 1569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12860 : Bounds (450438473 / 1000000000) (225219237 / 500000000) (Real.log (1569 / 1000)) := by
  have h := reflection_log_12860_neg
  have he : Real.log (1569 / 1000) = -Real.log (1000 / 1569) := by
    rw [show ((1569 / 1000) : ℝ) = ((1000 / 1569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12861_neg : (210411797 / 250000000) ≤ -Real.log (431 / 1000) ∧
    -Real.log (431 / 1000) ≤ (84164719 / 100000000) := by
  have h := checkLog_sound (w := (69 / 931)) (n := 12)
    (lo := (18562501 / 125000000)) (hi := (148500009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 431) = 1/(431 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12861 : Bounds (-84164719 / 100000000) (-210411797 / 250000000) (Real.log (431 / 1000)) := by
  have h := reflection_log_12861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12862_neg : (284419 / 500000000) ≤ -Real.log (1000000 / 1000569) ∧
    -Real.log (1000000 / 1000569) ≤ (568839 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 2000569)) (n := 12)
    (lo := (284419 / 500000000)) (hi := (568839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000569 / 1000000) = 1/(1000000 / 1000569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12862 : Bounds (284419 / 500000000) (568839 / 1000000000) (Real.log (1000569 / 1000000)) := by
  have h := reflection_log_12862_neg
  have he : Real.log (1000569 / 1000000) = -Real.log (1000000 / 1000569) := by
    rw [show ((1000569 / 1000000) : ℝ) = ((1000000 / 1000569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12863_neg : (569161 / 1000000000) ≤ -Real.log (999431 / 1000000) ∧
    -Real.log (999431 / 1000000) ≤ (284581 / 500000000) := by
  have h := checkLog_sound (w := (569 / 1999431)) (n := 12)
    (lo := (569161 / 1000000000)) (hi := (284581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999431) = 1/(999431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12863 : Bounds (-284581 / 500000000) (-569161 / 1000000000) (Real.log (999431 / 1000000)) := by
  have h := reflection_log_12863_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0201 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12864_neg : (131518557 / 500000000) ≤ -Real.log (8000 / 10407) ∧
    -Real.log (8000 / 10407) ≤ (52607423 / 200000000) := by
  have h := checkLog_sound (w := (2407 / 18407)) (n := 12)
    (lo := (131518557 / 500000000)) (hi := (52607423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10407 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10407 / 8000) = 1/(8000 / 10407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12864 : Bounds (131518557 / 500000000) (52607423 / 200000000) (Real.log (10407 / 8000)) := by
  have h := reflection_log_12864_neg
  have he : Real.log (10407 / 8000) = -Real.log (8000 / 10407) := by
    rw [show ((10407 / 8000) : ℝ) = ((8000 / 10407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12865_neg : (14317029 / 40000000) ≤ -Real.log (5593 / 8000) ∧
    -Real.log (5593 / 8000) ≤ (178962863 / 500000000) := by
  have h := checkLog_sound (w := (2407 / 13593)) (n := 12)
    (lo := (14317029 / 40000000)) (hi := (178962863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5593) = 1/(5593 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12865 : Bounds (-178962863 / 500000000) (-14317029 / 40000000) (Real.log (5593 / 8000)) := by
  have h := reflection_log_12865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12866_neg : (264835823 / 1000000000) ≤ -Real.log (1000000 / 1303217) ∧
    -Real.log (1000000 / 1303217) ≤ (16552239 / 62500000) := by
  have h := checkLog_sound (w := (303217 / 2303217)) (n := 12)
    (lo := (264835823 / 1000000000)) (hi := (16552239 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303217 / 1000000) = 1/(1000000 / 1303217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12866 : Bounds (264835823 / 1000000000) (16552239 / 62500000) (Real.log (1303217 / 1000000)) := by
  have h := reflection_log_12866_neg
  have he : Real.log (1303217 / 1000000) = -Real.log (1000000 / 1303217) := by
    rw [show ((1303217 / 1000000) : ℝ) = ((1000000 / 1303217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12867_neg : (11561 / 32000) ≤ -Real.log (696783 / 1000000) ∧
    -Real.log (696783 / 1000000) ≤ (361281251 / 1000000000) := by
  have h := checkLog_sound (w := (303217 / 1696783)) (n := 12)
    (lo := (11561 / 32000)) (hi := (361281251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696783) = 1/(696783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12867 : Bounds (-361281251 / 1000000000) (-11561 / 32000) (Real.log (696783 / 1000000)) := by
  have h := reflection_log_12867_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12868_neg : (96445427 / 1000000000) ≤ -Real.log (908059450911 / 1000000000000) ∧
    -Real.log (908059450911 / 1000000000000) ≤ (24111357 / 250000000) := by
  have h := checkLog_sound (w := (91940549089 / 1908059450911)) (n := 12)
    (lo := (96445427 / 1000000000)) (hi := (24111357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 908059450911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 908059450911) = 1/(908059450911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12868 : Bounds (-24111357 / 250000000) (-96445427 / 1000000000) (Real.log (908059450911 / 1000000000000)) := by
  have h := reflection_log_12868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12869_neg : (9488861 / 100000000) ≤ -Real.log (58206351 / 64000000) ∧
    -Real.log (58206351 / 64000000) ≤ (94888611 / 1000000000) := by
  have h := checkLog_sound (w := (5793649 / 122206351)) (n := 12)
    (lo := (9488861 / 100000000)) (hi := (94888611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 58206351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 58206351) = 1/(58206351 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12869 : Bounds (-94888611 / 1000000000) (-9488861 / 100000000) (Real.log (58206351 / 64000000)) := by
  have h := reflection_log_12869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12870_neg : (15524071 / 25000000) ≤ -Real.log (500000000000 / 930359377793) ∧
    -Real.log (500000000000 / 930359377793) ≤ (620962841 / 1000000000) := by
  have h := checkLog_sound (w := (430359377793 / 1430359377793)) (n := 12)
    (lo := (15524071 / 25000000)) (hi := (620962841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930359377793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930359377793 / 500000000000) = 1/(500000000000 / 930359377793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12870 : Bounds (15524071 / 25000000) (620962841 / 1000000000) (Real.log (930359377793 / 500000000000)) := by
  have h := reflection_log_12870_neg
  have he : Real.log (930359377793 / 500000000000) = -Real.log (500000000000 / 930359377793) := by
    rw [show ((930359377793 / 500000000000) : ℝ) = ((500000000000 / 930359377793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12871_neg : (313058537 / 500000000) ≤ -Real.log (500000000000 / 935167046269) ∧
    -Real.log (500000000000 / 935167046269) ≤ (25044683 / 40000000) := by
  have h := checkLog_sound (w := (435167046269 / 1435167046269)) (n := 12)
    (lo := (313058537 / 500000000)) (hi := (25044683 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935167046269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935167046269 / 500000000000) = 1/(500000000000 / 935167046269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12871 : Bounds (313058537 / 500000000) (25044683 / 40000000) (Real.log (935167046269 / 500000000000)) := by
  have h := reflection_log_12871_neg
  have he : Real.log (935167046269 / 500000000000) = -Real.log (500000000000 / 935167046269) := by
    rw [show ((935167046269 / 500000000000) : ℝ) = ((500000000000 / 935167046269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12872_neg : (1283235341 / 1000000000) ≤ -Real.log (500000000000 / 1804147465437) ∧
    -Real.log (500000000000 / 1804147465437) ≤ (1283235343 / 1000000000) := by
  have h := checkLog_sound (w := (804147465437 / 2804147465437)) (n := 12)
    (lo := (590088161 / 1000000000)) (hi := (295044081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1804147465437 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1804147465437 / 1000000000000) = 1/(500000000000 / 1804147465437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12872 : Bounds (1283235341 / 1000000000) (1283235343 / 1000000000) (Real.log (1804147465437 / 500000000000)) := by
  have h := reflection_log_12872_neg
  have he : Real.log (1804147465437 / 500000000000) = -Real.log (500000000000 / 1804147465437) := by
    rw [show ((1804147465437 / 500000000000) : ℝ) = ((500000000000 / 1804147465437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12873_neg : (646042831 / 500000000) ≤ -Real.log (10000000000 / 36403712297) ∧
    -Real.log (10000000000 / 36403712297) ≤ (40377677 / 31250000) := by
  have h := checkLog_sound (w := (16403712297 / 56403712297)) (n := 12)
    (lo := (299469241 / 500000000)) (hi := (598938483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36403712297 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(36403712297 / 20000000000) = 1/(10000000000 / 36403712297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12873 : Bounds (646042831 / 500000000) (40377677 / 31250000) (Real.log (36403712297 / 10000000000)) := by
  have h := reflection_log_12873_neg
  have he : Real.log (36403712297 / 10000000000) = -Real.log (10000000000 / 36403712297) := by
    rw [show ((36403712297 / 10000000000) : ℝ) = ((10000000000 / 36403712297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12874_neg : (226174347 / 500000000) ≤ -Real.log (250 / 393) ∧
    -Real.log (250 / 393) ≤ (90469739 / 200000000) := by
  have h := checkLog_sound (w := (143 / 643)) (n := 12)
    (lo := (226174347 / 500000000)) (hi := (90469739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 250) = 1/(250 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12874 : Bounds (226174347 / 500000000) (90469739 / 200000000) (Real.log (393 / 250)) := by
  have h := reflection_log_12874_neg
  have he : Real.log (393 / 250) = -Real.log (250 / 393) := by
    rw [show ((393 / 250) : ℝ) = ((250 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12875_neg : (424316041 / 500000000) ≤ -Real.log (107 / 250) ∧
    -Real.log (107 / 250) ≤ (212158021 / 250000000) := by
  have h := checkLog_sound (w := (9 / 116)) (n := 12)
    (lo := (77742451 / 500000000)) (hi := (155484903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 107) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 107) = 1/(107 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12875 : Bounds (-212158021 / 250000000) (-424316041 / 500000000) (Real.log (107 / 250)) := by
  have h := reflection_log_12875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12876_neg : (142959 / 250000000) ≤ -Real.log (250000 / 250143) ∧
    -Real.log (250000 / 250143) ≤ (571837 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 500143)) (n := 12)
    (lo := (142959 / 250000000)) (hi := (571837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250143 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250143 / 250000) = 1/(250000 / 250143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12876 : Bounds (142959 / 250000000) (571837 / 1000000000) (Real.log (250143 / 250000)) := by
  have h := reflection_log_12876_neg
  have he : Real.log (250143 / 250000) = -Real.log (250000 / 250143) := by
    rw [show ((250143 / 250000) : ℝ) = ((250000 / 250143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12877_neg : (572163 / 1000000000) ≤ -Real.log (249857 / 250000) ∧
    -Real.log (249857 / 250000) ≤ (143041 / 250000000) := by
  have h := checkLog_sound (w := (143 / 499857)) (n := 12)
    (lo := (572163 / 1000000000)) (hi := (143041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249857) = 1/(249857 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12877 : Bounds (-143041 / 250000000) (-572163 / 1000000000) (Real.log (249857 / 250000)) := by
  have h := reflection_log_12877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12878_neg : (132214527 / 500000000) ≤ -Real.log (1000000 / 1302687) ∧
    -Real.log (1000000 / 1302687) ≤ (52885811 / 200000000) := by
  have h := checkLog_sound (w := (302687 / 2302687)) (n := 12)
    (lo := (132214527 / 500000000)) (hi := (52885811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302687 / 1000000) = 1/(1000000 / 1302687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12878 : Bounds (132214527 / 500000000) (52885811 / 200000000) (Real.log (1302687 / 1000000)) := by
  have h := reflection_log_12878_neg
  have he : Real.log (1302687 / 1000000) = -Real.log (1000000 / 1302687) := by
    rw [show ((1302687 / 1000000) : ℝ) = ((1000000 / 1302687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12879_neg : (360520901 / 1000000000) ≤ -Real.log (697313 / 1000000) ∧
    -Real.log (697313 / 1000000) ≤ (180260451 / 500000000) := by
  have h := checkLog_sound (w := (302687 / 1697313)) (n := 12)
    (lo := (360520901 / 1000000000)) (hi := (180260451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697313) = 1/(697313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12879 : Bounds (-180260451 / 500000000) (-360520901 / 1000000000) (Real.log (697313 / 1000000)) := by
  have h := reflection_log_12879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12880_neg : (13311493 / 50000000) ≤ -Real.log (200000 / 261007) ∧
    -Real.log (200000 / 261007) ≤ (266229861 / 1000000000) := by
  have h := checkLog_sound (w := (61007 / 461007)) (n := 12)
    (lo := (13311493 / 50000000)) (hi := (266229861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261007 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261007 / 200000) = 1/(200000 / 261007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12880 : Bounds (13311493 / 50000000) (266229861 / 1000000000) (Real.log (261007 / 200000)) := by
  have h := reflection_log_12880_neg
  have he : Real.log (261007 / 200000) = -Real.log (200000 / 261007) := by
    rw [show ((261007 / 200000) : ℝ) = ((200000 / 261007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12881_neg : (181946897 / 500000000) ≤ -Real.log (138993 / 200000) ∧
    -Real.log (138993 / 200000) ≤ (72778759 / 200000000) := by
  have h := checkLog_sound (w := (61007 / 338993)) (n := 12)
    (lo := (181946897 / 500000000)) (hi := (72778759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138993) = 1/(138993 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12881 : Bounds (-72778759 / 200000000) (-181946897 / 500000000) (Real.log (138993 / 200000)) := by
  have h := reflection_log_12881_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12882_neg : (48831967 / 500000000) ≤ -Real.log (36278145951 / 40000000000) ∧
    -Real.log (36278145951 / 40000000000) ≤ (19532787 / 200000000) := by
  have h := checkLog_sound (w := (3721854049 / 76278145951)) (n := 12)
    (lo := (48831967 / 500000000)) (hi := (19532787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 36278145951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 36278145951) = 1/(36278145951 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12882 : Bounds (-19532787 / 200000000) (-48831967 / 500000000) (Real.log (36278145951 / 40000000000)) := by
  have h := reflection_log_12882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12883_neg : (96091847 / 1000000000) ≤ -Real.log (908380580031 / 1000000000000) ∧
    -Real.log (908380580031 / 1000000000000) ≤ (12011481 / 125000000) := by
  have h := checkLog_sound (w := (91619419969 / 1908380580031)) (n := 12)
    (lo := (96091847 / 1000000000)) (hi := (12011481 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 908380580031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 908380580031) = 1/(908380580031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12883 : Bounds (-12011481 / 125000000) (-96091847 / 1000000000) (Real.log (908380580031 / 1000000000000)) := by
  have h := reflection_log_12883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12884_neg : (124989991 / 200000000) ≤ -Real.log (31250000000 / 58379764539) ∧
    -Real.log (31250000000 / 58379764539) ≤ (156237489 / 250000000) := by
  have h := checkLog_sound (w := (27129764539 / 89629764539)) (n := 12)
    (lo := (124989991 / 200000000)) (hi := (156237489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58379764539 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58379764539 / 31250000000) = 1/(31250000000 / 58379764539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12884 : Bounds (124989991 / 200000000) (156237489 / 250000000) (Real.log (58379764539 / 31250000000)) := by
  have h := reflection_log_12884_neg
  have he : Real.log (58379764539 / 31250000000) = -Real.log (31250000000 / 58379764539) := by
    rw [show ((58379764539 / 31250000000) : ℝ) = ((31250000000 / 58379764539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12885_neg : (315061827 / 500000000) ≤ -Real.log (500000000000 / 938921384531) ∧
    -Real.log (500000000000 / 938921384531) ≤ (126024731 / 200000000) := by
  have h := checkLog_sound (w := (438921384531 / 1438921384531)) (n := 12)
    (lo := (315061827 / 500000000)) (hi := (126024731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938921384531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938921384531 / 500000000000) = 1/(500000000000 / 938921384531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12885 : Bounds (315061827 / 500000000) (126024731 / 200000000) (Real.log (938921384531 / 500000000000)) := by
  have h := reflection_log_12885_neg
  have he : Real.log (938921384531 / 500000000000) = -Real.log (500000000000 / 938921384531) := by
    rw [show ((938921384531 / 500000000000) : ℝ) = ((500000000000 / 938921384531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12886_neg : (646042831 / 500000000) ≤ -Real.log (500000000000 / 1820185614849) ∧
    -Real.log (500000000000 / 1820185614849) ≤ (40377677 / 31250000) := by
  have h := checkLog_sound (w := (820185614849 / 2820185614849)) (n := 12)
    (lo := (299469241 / 500000000)) (hi := (598938483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1820185614849 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1820185614849 / 1000000000000) = 1/(500000000000 / 1820185614849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12886 : Bounds (646042831 / 500000000) (40377677 / 31250000) (Real.log (1820185614849 / 500000000000)) := by
  have h := reflection_log_12886_neg
  have he : Real.log (1820185614849 / 500000000000) = -Real.log (500000000000 / 1820185614849) := by
    rw [show ((1820185614849 / 500000000000) : ℝ) = ((500000000000 / 1820185614849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12887_neg : (162622597 / 125000000) ≤ -Real.log (500000000000 / 1836448598131) ∧
    -Real.log (500000000000 / 1836448598131) ≤ (650490389 / 500000000) := by
  have h := checkLog_sound (w := (836448598131 / 2836448598131)) (n := 12)
    (lo := (151958399 / 250000000)) (hi := (607833597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1836448598131 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1836448598131 / 1000000000000) = 1/(500000000000 / 1836448598131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12887 : Bounds (162622597 / 125000000) (650490389 / 500000000) (Real.log (1836448598131 / 500000000000)) := by
  have h := reflection_log_12887_neg
  have he : Real.log (1836448598131 / 500000000000) = -Real.log (500000000000 / 1836448598131) := by
    rw [show ((1836448598131 / 500000000000) : ℝ) = ((500000000000 / 1836448598131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12888_neg : (56781909 / 125000000) ≤ -Real.log (40 / 63) ∧
    -Real.log (40 / 63) ≤ (454255273 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 103)) (n := 12)
    (lo := (56781909 / 125000000)) (hi := (454255273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 40) = 1/(40 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12888 : Bounds (56781909 / 125000000) (454255273 / 1000000000) (Real.log (63 / 40)) := by
  have h := reflection_log_12888_neg
  have he : Real.log (63 / 40) = -Real.log (40 / 63) := by
    rw [show ((63 / 40) : ℝ) = ((40 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12889_neg : (855666109 / 1000000000) ≤ -Real.log (17 / 40) ∧
    -Real.log (17 / 40) ≤ (855666111 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 17) = 1/(17 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12889 : Bounds (-855666111 / 1000000000) (-855666109 / 1000000000) (Real.log (17 / 40)) := by
  have h := reflection_log_12889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12890_neg : (287417 / 500000000) ≤ -Real.log (40000 / 40023) ∧
    -Real.log (40000 / 40023) ≤ (114967 / 200000000) := by
  have h := checkLog_sound (w := (23 / 80023)) (n := 12)
    (lo := (287417 / 500000000)) (hi := (114967 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40023 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40023 / 40000) = 1/(40000 / 40023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12890 : Bounds (287417 / 500000000) (114967 / 200000000) (Real.log (40023 / 40000)) := by
  have h := reflection_log_12890_neg
  have he : Real.log (40023 / 40000) = -Real.log (40000 / 40023) := by
    rw [show ((40023 / 40000) : ℝ) = ((40000 / 40023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12891_neg : (115033 / 200000000) ≤ -Real.log (39977 / 40000) ∧
    -Real.log (39977 / 40000) ≤ (287583 / 500000000) := by
  have h := checkLog_sound (w := (23 / 79977)) (n := 12)
    (lo := (115033 / 200000000)) (hi := (287583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39977) = 1/(39977 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12891 : Bounds (-287583 / 500000000) (-115033 / 200000000) (Real.log (39977 / 40000)) := by
  have h := reflection_log_12891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12892_neg : (2126577 / 8000000) ≤ -Real.log (1000000 / 1304503) ∧
    -Real.log (1000000 / 1304503) ≤ (132911063 / 500000000) := by
  have h := checkLog_sound (w := (304503 / 2304503)) (n := 12)
    (lo := (2126577 / 8000000)) (hi := (132911063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304503 / 1000000) = 1/(1000000 / 1304503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12892 : Bounds (2126577 / 8000000) (132911063 / 500000000) (Real.log (1304503 / 1000000)) := by
  have h := reflection_log_12892_neg
  have he : Real.log (1304503 / 1000000) = -Real.log (1000000 / 1304503) := by
    rw [show ((1304503 / 1000000) : ℝ) = ((1000000 / 1304503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12893_neg : (363128581 / 1000000000) ≤ -Real.log (695497 / 1000000) ∧
    -Real.log (695497 / 1000000) ≤ (181564291 / 500000000) := by
  have h := checkLog_sound (w := (304503 / 1695497)) (n := 12)
    (lo := (363128581 / 1000000000)) (hi := (181564291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695497) = 1/(695497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12893 : Bounds (-181564291 / 500000000) (-363128581 / 1000000000) (Real.log (695497 / 1000000)) := by
  have h := reflection_log_12893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12894_neg : (267625017 / 1000000000) ≤ -Real.log (1000000 / 1306857) ∧
    -Real.log (1000000 / 1306857) ≤ (133812509 / 500000000) := by
  have h := checkLog_sound (w := (306857 / 2306857)) (n := 12)
    (lo := (267625017 / 1000000000)) (hi := (133812509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306857 / 1000000) = 1/(1000000 / 1306857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12894 : Bounds (267625017 / 1000000000) (133812509 / 500000000) (Real.log (1306857 / 1000000)) := by
  have h := reflection_log_12894_neg
  have he : Real.log (1306857 / 1000000) = -Real.log (1000000 / 1306857) := by
    rw [show ((1306857 / 1000000) : ℝ) = ((1000000 / 1306857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12895_neg : (366518951 / 1000000000) ≤ -Real.log (693143 / 1000000) ∧
    -Real.log (693143 / 1000000) ≤ (45814869 / 125000000) := by
  have h := checkLog_sound (w := (306857 / 1693143)) (n := 12)
    (lo := (366518951 / 1000000000)) (hi := (45814869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693143) = 1/(693143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12895 : Bounds (-45814869 / 125000000) (-366518951 / 1000000000) (Real.log (693143 / 1000000)) := by
  have h := reflection_log_12895_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12896_neg : (49446967 / 500000000) ≤ -Real.log (905838781551 / 1000000000000) ∧
    -Real.log (905838781551 / 1000000000000) ≤ (19778787 / 200000000) := by
  have h := checkLog_sound (w := (94161218449 / 1905838781551)) (n := 12)
    (lo := (49446967 / 500000000)) (hi := (19778787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 905838781551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 905838781551) = 1/(905838781551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12896 : Bounds (-19778787 / 200000000) (-49446967 / 500000000) (Real.log (905838781551 / 1000000000000)) := by
  have h := reflection_log_12896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12897_neg : (19461291 / 200000000) ≤ -Real.log (907277922991 / 1000000000000) ∧
    -Real.log (907277922991 / 1000000000000) ≤ (12163307 / 125000000) := by
  have h := checkLog_sound (w := (92722077009 / 1907277922991)) (n := 12)
    (lo := (19461291 / 200000000)) (hi := (12163307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 907277922991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 907277922991) = 1/(907277922991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12897 : Bounds (-12163307 / 125000000) (-19461291 / 200000000) (Real.log (907277922991 / 1000000000000)) := by
  have h := reflection_log_12897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12898_neg : (314475353 / 500000000) ≤ -Real.log (100000000000 / 187564144777) ∧
    -Real.log (100000000000 / 187564144777) ≤ (628950707 / 1000000000) := by
  have h := checkLog_sound (w := (87564144777 / 287564144777)) (n := 12)
    (lo := (314475353 / 500000000)) (hi := (628950707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187564144777 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187564144777 / 100000000000) = 1/(100000000000 / 187564144777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12898 : Bounds (314475353 / 500000000) (628950707 / 1000000000) (Real.log (187564144777 / 100000000000)) := by
  have h := reflection_log_12898_neg
  have he : Real.log (187564144777 / 100000000000) = -Real.log (100000000000 / 187564144777) := by
    rw [show ((187564144777 / 100000000000) : ℝ) = ((100000000000 / 187564144777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12899_neg : (634143969 / 1000000000) ≤ -Real.log (50000000000 / 94270374223) ∧
    -Real.log (50000000000 / 94270374223) ≤ (63414397 / 100000000) := by
  have h := checkLog_sound (w := (44270374223 / 144270374223)) (n := 12)
    (lo := (634143969 / 1000000000)) (hi := (63414397 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94270374223 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94270374223 / 50000000000) = 1/(50000000000 / 94270374223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12899 : Bounds (634143969 / 1000000000) (63414397 / 100000000) (Real.log (94270374223 / 50000000000)) := by
  have h := reflection_log_12899_neg
  have he : Real.log (94270374223 / 50000000000) = -Real.log (50000000000 / 94270374223) := by
    rw [show ((94270374223 / 50000000000) : ℝ) = ((50000000000 / 94270374223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12900_neg : (162622597 / 125000000) ≤ -Real.log (50000000000 / 183644859813) ∧
    -Real.log (50000000000 / 183644859813) ≤ (650490389 / 500000000) := by
  have h := checkLog_sound (w := (83644859813 / 283644859813)) (n := 12)
    (lo := (151958399 / 250000000)) (hi := (607833597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183644859813 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(183644859813 / 100000000000) = 1/(50000000000 / 183644859813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12900 : Bounds (162622597 / 125000000) (650490389 / 500000000) (Real.log (183644859813 / 50000000000)) := by
  have h := reflection_log_12900_neg
  have he : Real.log (183644859813 / 50000000000) = -Real.log (50000000000 / 183644859813) := by
    rw [show ((183644859813 / 50000000000) : ℝ) = ((50000000000 / 183644859813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12901_neg : (1309921381 / 1000000000) ≤ -Real.log (500000000000 / 1852941176471) ∧
    -Real.log (500000000000 / 1852941176471) ≤ (1309921383 / 1000000000) := by
  have h := checkLog_sound (w := (852941176471 / 2852941176471)) (n := 12)
    (lo := (616774201 / 1000000000)) (hi := (308387101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1852941176471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1852941176471 / 1000000000000) = 1/(500000000000 / 1852941176471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12901 : Bounds (1309921381 / 1000000000) (1309921383 / 1000000000) (Real.log (1852941176471 / 500000000000)) := by
  have h := reflection_log_12901_neg
  have he : Real.log (1852941176471 / 500000000000) = -Real.log (500000000000 / 1852941176471) := by
    rw [show ((1852941176471 / 500000000000) : ℝ) = ((500000000000 / 1852941176471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12902_neg : (228079111 / 500000000) ≤ -Real.log (500 / 789) ∧
    -Real.log (500 / 789) ≤ (456158223 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1289)) (n := 12)
    (lo := (228079111 / 500000000)) (hi := (456158223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789 / 500) = 1/(500 / 789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12902 : Bounds (228079111 / 500000000) (456158223 / 1000000000) (Real.log (789 / 500)) := by
  have h := reflection_log_12902_neg
  have he : Real.log (789 / 500) = -Real.log (500 / 789) := by
    rw [show ((789 / 500) : ℝ) = ((500 / 789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12903_neg : (215687491 / 250000000) ≤ -Real.log (211 / 500) ∧
    -Real.log (211 / 500) ≤ (431374983 / 500000000) := by
  have h := checkLog_sound (w := (39 / 461)) (n := 12)
    (lo := (5300087 / 31250000)) (hi := (33920557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 211) = 1/(211 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12903 : Bounds (-431374983 / 500000000) (-215687491 / 250000000) (Real.log (211 / 500)) := by
  have h := reflection_log_12903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12904_neg : (577833 / 1000000000) ≤ -Real.log (500000 / 500289) ∧
    -Real.log (500000 / 500289) ≤ (288917 / 500000000) := by
  have h := checkLog_sound (w := (289 / 1000289)) (n := 12)
    (lo := (577833 / 1000000000)) (hi := (288917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500289 / 500000) = 1/(500000 / 500289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12904 : Bounds (577833 / 1000000000) (288917 / 500000000) (Real.log (500289 / 500000)) := by
  have h := reflection_log_12904_neg
  have he : Real.log (500289 / 500000) = -Real.log (500000 / 500289) := by
    rw [show ((500289 / 500000) : ℝ) = ((500000 / 500289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12905_neg : (578167 / 1000000000) ≤ -Real.log (499711 / 500000) ∧
    -Real.log (499711 / 500000) ≤ (72271 / 125000000) := by
  have h := checkLog_sound (w := (289 / 999711)) (n := 12)
    (lo := (578167 / 1000000000)) (hi := (72271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499711) = 1/(499711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12905 : Bounds (-72271 / 125000000) (-578167 / 1000000000) (Real.log (499711 / 500000)) := by
  have h := reflection_log_12905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12906_neg : (835051 / 3125000) ≤ -Real.log (1000000 / 1306323) ∧
    -Real.log (1000000 / 1306323) ≤ (267216321 / 1000000000) := by
  have h := checkLog_sound (w := (306323 / 2306323)) (n := 12)
    (lo := (835051 / 3125000)) (hi := (267216321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306323 / 1000000) = 1/(1000000 / 1306323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12906 : Bounds (835051 / 3125000) (267216321 / 1000000000) (Real.log (1306323 / 1000000)) := by
  have h := reflection_log_12906_neg
  have he : Real.log (1306323 / 1000000) = -Real.log (1000000 / 1306323) := by
    rw [show ((1306323 / 1000000) : ℝ) = ((1000000 / 1306323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12907_neg : (91437211 / 250000000) ≤ -Real.log (693677 / 1000000) ∧
    -Real.log (693677 / 1000000) ≤ (73149769 / 200000000) := by
  have h := checkLog_sound (w := (306323 / 1693677)) (n := 12)
    (lo := (91437211 / 250000000)) (hi := (73149769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693677) = 1/(693677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12907 : Bounds (-73149769 / 200000000) (-91437211 / 250000000) (Real.log (693677 / 1000000)) := by
  have h := reflection_log_12907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12908_neg : (33627661 / 125000000) ≤ -Real.log (1000000 / 1308683) ∧
    -Real.log (1000000 / 1308683) ≤ (269021289 / 1000000000) := by
  have h := checkLog_sound (w := (308683 / 2308683)) (n := 12)
    (lo := (33627661 / 125000000)) (hi := (269021289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1308683 / 1000000) = 1/(1000000 / 1308683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12908 : Bounds (33627661 / 125000000) (269021289 / 1000000000) (Real.log (1308683 / 1000000)) := by
  have h := reflection_log_12908_neg
  have he : Real.log (1308683 / 1000000) = -Real.log (1000000 / 1308683) := by
    rw [show ((1308683 / 1000000) : ℝ) = ((1000000 / 1308683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12909_neg : (92289201 / 250000000) ≤ -Real.log (691317 / 1000000) ∧
    -Real.log (691317 / 1000000) ≤ (73831361 / 200000000) := by
  have h := checkLog_sound (w := (308683 / 1691317)) (n := 12)
    (lo := (92289201 / 250000000)) (hi := (73831361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 691317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 691317) = 1/(691317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12909 : Bounds (-73831361 / 200000000) (-92289201 / 250000000) (Real.log (691317 / 1000000)) := by
  have h := reflection_log_12909_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12910_neg : (25033879 / 250000000) ≤ -Real.log (904714805511 / 1000000000000) ∧
    -Real.log (904714805511 / 1000000000000) ≤ (100135517 / 1000000000) := by
  have h := checkLog_sound (w := (95285194489 / 1904714805511)) (n := 12)
    (lo := (25033879 / 250000000)) (hi := (100135517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 904714805511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 904714805511) = 1/(904714805511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12910 : Bounds (-100135517 / 1000000000) (-25033879 / 250000000) (Real.log (904714805511 / 1000000000000)) := by
  have h := reflection_log_12910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12911_neg : (24633131 / 250000000) ≤ -Real.log (906166219671 / 1000000000000) ∧
    -Real.log (906166219671 / 1000000000000) ≤ (3941301 / 40000000) := by
  have h := checkLog_sound (w := (93833780329 / 1906166219671)) (n := 12)
    (lo := (24633131 / 250000000)) (hi := (3941301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 906166219671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 906166219671) = 1/(906166219671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12911 : Bounds (-3941301 / 40000000) (-24633131 / 250000000) (Real.log (906166219671 / 1000000000000)) := by
  have h := reflection_log_12911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12912_neg : (126593033 / 200000000) ≤ -Real.log (500000000000 / 941593133403) ∧
    -Real.log (500000000000 / 941593133403) ≤ (316482583 / 500000000) := by
  have h := checkLog_sound (w := (441593133403 / 1441593133403)) (n := 12)
    (lo := (126593033 / 200000000)) (hi := (316482583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941593133403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941593133403 / 500000000000) = 1/(500000000000 / 941593133403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12912 : Bounds (126593033 / 200000000) (316482583 / 500000000) (Real.log (941593133403 / 500000000000)) := by
  have h := reflection_log_12912_neg
  have he : Real.log (941593133403 / 500000000000) = -Real.log (500000000000 / 941593133403) := by
    rw [show ((941593133403 / 500000000000) : ℝ) = ((500000000000 / 941593133403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12913_neg : (159544523 / 250000000) ≤ -Real.log (500000000000 / 946514406561) ∧
    -Real.log (500000000000 / 946514406561) ≤ (638178093 / 1000000000) := by
  have h := checkLog_sound (w := (446514406561 / 1446514406561)) (n := 12)
    (lo := (159544523 / 250000000)) (hi := (638178093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((946514406561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(946514406561 / 500000000000) = 1/(500000000000 / 946514406561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12913 : Bounds (159544523 / 250000000) (638178093 / 1000000000) (Real.log (946514406561 / 500000000000)) := by
  have h := reflection_log_12913_neg
  have he : Real.log (946514406561 / 500000000000) = -Real.log (500000000000 / 946514406561) := by
    rw [show ((946514406561 / 500000000000) : ℝ) = ((500000000000 / 946514406561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12914_neg : (1309921381 / 1000000000) ≤ -Real.log (50000000000 / 185294117647) ∧
    -Real.log (50000000000 / 185294117647) ≤ (1309921383 / 1000000000) := by
  have h := checkLog_sound (w := (85294117647 / 285294117647)) (n := 12)
    (lo := (616774201 / 1000000000)) (hi := (308387101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185294117647 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(185294117647 / 100000000000) = 1/(50000000000 / 185294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12914 : Bounds (1309921381 / 1000000000) (1309921383 / 1000000000) (Real.log (185294117647 / 50000000000)) := by
  have h := reflection_log_12914_neg
  have he : Real.log (185294117647 / 50000000000) = -Real.log (50000000000 / 185294117647) := by
    rw [show ((185294117647 / 50000000000) : ℝ) = ((50000000000 / 185294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12915_neg : (659454093 / 500000000) ≤ -Real.log (250000000000 / 934834123223) ∧
    -Real.log (250000000000 / 934834123223) ≤ (329727047 / 250000000) := by
  have h := checkLog_sound (w := (434834123223 / 1434834123223)) (n := 12)
    (lo := (312880503 / 500000000)) (hi := (625761007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934834123223 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(934834123223 / 500000000000) = 1/(250000000000 / 934834123223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12915 : Bounds (659454093 / 500000000) (329727047 / 250000000) (Real.log (934834123223 / 250000000000)) := by
  have h := reflection_log_12915_neg
  have he : Real.log (934834123223 / 250000000000) = -Real.log (250000000000 / 934834123223) := by
    rw [show ((934834123223 / 250000000000) : ℝ) = ((250000000000 / 934834123223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12916_neg : (229028779 / 500000000) ≤ -Real.log (1000 / 1581) ∧
    -Real.log (1000 / 1581) ≤ (458057559 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 2581)) (n := 12)
    (lo := (229028779 / 500000000)) (hi := (458057559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1581 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1581 / 1000) = 1/(1000 / 1581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12916 : Bounds (229028779 / 500000000) (458057559 / 1000000000) (Real.log (1581 / 1000)) := by
  have h := reflection_log_12916_neg
  have he : Real.log (1581 / 1000) = -Real.log (1000 / 1581) := by
    rw [show ((1581 / 1000) : ℝ) = ((1000 / 1581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12917_neg : (434942179 / 500000000) ≤ -Real.log (419 / 1000) ∧
    -Real.log (419 / 1000) ≤ (21747109 / 25000000) := by
  have h := checkLog_sound (w := (81 / 919)) (n := 12)
    (lo := (88368589 / 500000000)) (hi := (176737179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 419) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 419) = 1/(419 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12917 : Bounds (-21747109 / 25000000) (-434942179 / 500000000) (Real.log (419 / 1000)) := by
  have h := reflection_log_12917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12918_neg : (580831 / 1000000000) ≤ -Real.log (1000000 / 1000581) ∧
    -Real.log (1000000 / 1000581) ≤ (18151 / 31250000) := by
  have h := checkLog_sound (w := (581 / 2000581)) (n := 12)
    (lo := (580831 / 1000000000)) (hi := (18151 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000581 / 1000000) = 1/(1000000 / 1000581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12918 : Bounds (580831 / 1000000000) (18151 / 31250000) (Real.log (1000581 / 1000000)) := by
  have h := reflection_log_12918_neg
  have he : Real.log (1000581 / 1000000) = -Real.log (1000000 / 1000581) := by
    rw [show ((1000581 / 1000000) : ℝ) = ((1000000 / 1000581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12919_neg : (36323 / 62500000) ≤ -Real.log (999419 / 1000000) ∧
    -Real.log (999419 / 1000000) ≤ (581169 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 1999419)) (n := 12)
    (lo := (36323 / 62500000)) (hi := (581169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999419) = 1/(999419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12919 : Bounds (-581169 / 1000000000) (-36323 / 62500000) (Real.log (999419 / 1000000)) := by
  have h := reflection_log_12919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12920_neg : (268610867 / 1000000000) ≤ -Real.log (500000 / 654073) ∧
    -Real.log (500000 / 654073) ≤ (67152717 / 250000000) := by
  have h := checkLog_sound (w := (154073 / 1154073)) (n := 12)
    (lo := (268610867 / 1000000000)) (hi := (67152717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654073 / 500000) = 1/(500000 / 654073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12920 : Bounds (268610867 / 1000000000) (67152717 / 250000000) (Real.log (654073 / 500000)) := by
  have h := reflection_log_12920_neg
  have he : Real.log (654073 / 500000) = -Real.log (500000 / 654073) := by
    rw [show ((654073 / 500000) : ℝ) = ((500000 / 654073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12921_neg : (46047541 / 125000000) ≤ -Real.log (345927 / 500000) ∧
    -Real.log (345927 / 500000) ≤ (368380329 / 1000000000) := by
  have h := checkLog_sound (w := (154073 / 845927)) (n := 12)
    (lo := (46047541 / 125000000)) (hi := (368380329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 345927) = 1/(345927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12921 : Bounds (-368380329 / 1000000000) (-46047541 / 125000000) (Real.log (345927 / 500000)) := by
  have h := reflection_log_12921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12922_neg : (54084343 / 200000000) ≤ -Real.log (1000000 / 1310517) ∧
    -Real.log (1000000 / 1310517) ≤ (67605429 / 250000000) := by
  have h := checkLog_sound (w := (310517 / 2310517)) (n := 12)
    (lo := (54084343 / 200000000)) (hi := (67605429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1310517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1310517 / 1000000) = 1/(1000000 / 1310517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12922 : Bounds (54084343 / 200000000) (67605429 / 250000000) (Real.log (1310517 / 1000000)) := by
  have h := reflection_log_12922_neg
  have he : Real.log (1310517 / 1000000) = -Real.log (1000000 / 1310517) := by
    rw [show ((1310517 / 1000000) : ℝ) = ((1000000 / 1310517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12923_neg : (371813237 / 1000000000) ≤ -Real.log (689483 / 1000000) ∧
    -Real.log (689483 / 1000000) ≤ (185906619 / 500000000) := by
  have h := checkLog_sound (w := (310517 / 1689483)) (n := 12)
    (lo := (371813237 / 1000000000)) (hi := (185906619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 689483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 689483) = 1/(689483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12923 : Bounds (-185906619 / 500000000) (-371813237 / 1000000000) (Real.log (689483 / 1000000)) := by
  have h := reflection_log_12923_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12924_neg : (101391521 / 1000000000) ≤ -Real.log (903579192711 / 1000000000000) ∧
    -Real.log (903579192711 / 1000000000000) ≤ (50695761 / 500000000) := by
  have h := checkLog_sound (w := (96420807289 / 1903579192711)) (n := 12)
    (lo := (101391521 / 1000000000)) (hi := (50695761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 903579192711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 903579192711) = 1/(903579192711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12924 : Bounds (-50695761 / 500000000) (-101391521 / 1000000000) (Real.log (903579192711 / 1000000000000)) := by
  have h := reflection_log_12924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12925_neg : (4988473 / 50000000) ≤ -Real.log (226261510671 / 250000000000) ∧
    -Real.log (226261510671 / 250000000000) ≤ (99769461 / 1000000000) := by
  have h := checkLog_sound (w := (23738489329 / 476261510671)) (n := 12)
    (lo := (4988473 / 50000000)) (hi := (99769461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 226261510671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 226261510671) = 1/(226261510671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12925 : Bounds (-99769461 / 1000000000) (-4988473 / 50000000) (Real.log (226261510671 / 250000000000)) := by
  have h := reflection_log_12925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12926_neg : (127398239 / 200000000) ≤ -Real.log (500000000000 / 945391657777) ∧
    -Real.log (500000000000 / 945391657777) ≤ (159247799 / 250000000) := by
  have h := checkLog_sound (w := (445391657777 / 1445391657777)) (n := 12)
    (lo := (127398239 / 200000000)) (hi := (159247799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945391657777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945391657777 / 500000000000) = 1/(500000000000 / 945391657777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12926 : Bounds (127398239 / 200000000) (159247799 / 250000000) (Real.log (945391657777 / 500000000000)) := by
  have h := reflection_log_12926_neg
  have he : Real.log (945391657777 / 500000000000) = -Real.log (500000000000 / 945391657777) := by
    rw [show ((945391657777 / 500000000000) : ℝ) = ((500000000000 / 945391657777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12927_neg : (642234953 / 1000000000) ≤ -Real.log (250000000000 / 475181041447) ∧
    -Real.log (250000000000 / 475181041447) ≤ (321117477 / 500000000) := by
  have h := checkLog_sound (w := (225181041447 / 725181041447)) (n := 12)
    (lo := (642234953 / 1000000000)) (hi := (321117477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475181041447 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475181041447 / 250000000000) = 1/(250000000000 / 475181041447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12927 : Bounds (642234953 / 1000000000) (321117477 / 500000000) (Real.log (475181041447 / 250000000000)) := by
  have h := reflection_log_12927_neg
  have he : Real.log (475181041447 / 250000000000) = -Real.log (250000000000 / 475181041447) := by
    rw [show ((475181041447 / 250000000000) : ℝ) = ((250000000000 / 475181041447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


