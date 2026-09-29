-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0123__7_q101
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0123__7_q101
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:47:47.76652+00:00
-- url     : https://prove2.me/theorems/17b61cc1-b768-461b-9081-e8015f2a83d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0125, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0126, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0127, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0128, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0129) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0125, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0126, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0127, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0128, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0129) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0125, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0126, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0127, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0128, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0129) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Cell0123 (+6 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Cell0124, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0125, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0126, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0127, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0128, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0129) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0123__7_q100

namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_129 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1629 / 10000):ℝ) ((163 / 1000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (403832168174929214162308599 / 1184539201319610125000000000) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hz1 : z < 1 := by linarith [hz.2]
  have hb0 : 0 ≤ a*z := mul_nonneg ha0.le hz.1
  have hb1 : a*z < 1 := by nlinarith [mul_pos ha0 (sub_pos.mpr hz1),ha1]
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    have h1 : 0 < biasE a := by
      rw [biasE_eq_binEntropy (by linarith) ha1]
      exact Real.binEntropy_pos (by linarith) (by linarith)
    have h2 : 0 ≤ biasE (a*z) := by
      rw [biasE_eq_binEntropy (by linarith) hb1]
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    linarith
  have hs0 : 0 < s := by
    have := mul_pos ha0 (sub_pos.mpr hz1)
    linarith [hs.1]
  have hsl : (1627371 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (163163 / 2000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (163 / 1000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_129 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

end GeneralCK.Certificates.LowRatioFamily


