-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SmallMeanFixed
-- name    : CK_GeneralCK_Certificates_SmallMeanFixed
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:09.731283+00:00
-- url     : https://prove2.me/theorems/dfbaeb9e-1d35-455c-96cf-76bf9a0d9e27
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SmallMeanFixed` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SmallMeanFixed` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SmallMeanFixed` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SmallMeanFixed (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SmallMeanFixed.lean)

import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanLeaves
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanSlopeBounds

namespace GeneralCK.Certificates.SmallMean

theorem fixed_inverse_bracket :
    (16282259 / 67108864) ≤ entropyInverse (1-H (1/32)) ∧
    entropyInverse (1-H (1/32)) ≤ (4070565 / 16777216) := by
  have ht := entropy_1
  have hl := entropy_6
  have hu := entropy_7
  exact inverse_bracket (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith only [ht.2, hl.2]) (by linarith only [ht.1, hu.1])

theorem fixed_logit_lower : (17786621 / 15625000) ≤ Real.log ((1-(4070565 / 16777216))/(4070565 / 16777216)) := by
  have hv := log_v_7.1
  have hc := log_c_7.2
  rw [Real.log_div (by norm_num) (by norm_num)]
  norm_num
  linarith only [hv, hc]

theorem fixed_secant_lt :
    (deriv Scalar.P (H (1/32))-4)/H (1/32) < (23/10 : ℝ) := by
  have ht := entropy_1
  have ht0 : 0 < H (1/32) := by linarith only [ht.1]
  have ht1 : H (1/32) < 1 := by linarith only [ht.2]
  have hb := slope_upper ht0 ht1 (l := (16282259 / 67108864)) (u := (4070565 / 16777216))
    (j := (17786621 / 15625000)) (by norm_num) (by norm_num)
    fixed_inverse_bracket.1 fixed_inverse_bracket.2 fixed_logit_lower (by norm_num)
  have hn : 2+(1-2*((16282259 / 67108864) : ℝ))/((16282259 / 67108864)*(1-(4070565 / 16777216))*(17786621 / 15625000))-4 <
      (23/10)*(200622323 / 1000000000) := by norm_num
  apply (div_lt_iff₀ ht0).mpr
  linarith only [hb, hn, ht.1]

end GeneralCK.Certificates.SmallMean


