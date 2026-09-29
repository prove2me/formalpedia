-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointLogGain
-- name    : CK_GeneralCK_PsiEndpointLogGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:19:44.536401+00:00
-- url     : https://prove2.me/theorems/14fa23bd-95bb-437a-8d45-3d8f201d823b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointLogGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointLogGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointLogGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointLogGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointLogGain.lean)

import Definitions.Def_CK_GeneralCK_PsiExtendedEntropyCurvature
import Definitions.Def_CK_GeneralCK_PsiSignedSplit

-- ===== source module GeneralCK.PsiEndpointLogGain =====
section

/-!+# Logarithmic entropy-imbalance gain at an endpoint contact

The inverse-entropy logit has quantitative curvature on `(0,1/4]`.
This range suffices for the ratio-eight endpoint argument and avoids the
additional fixed comparisons needed for the manuscript's ratio-five range.
-/

namespace GeneralCK.PsiEndpointLogGain
open Set Filter
open scoped Topology

noncomputable def Q (h : ℝ) : ℝ := J (entropyInverse h)
noncomputable def slope (h : ℝ) : ℝ :=
  -1 / (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h))
noncomputable def curvature (h : ℝ) : ℝ :=
  let v := entropyInverse h
  let l := Real.log ((1 - v) / v)
  Real.log 2 * ((1 - 2 * v) * l - 1) / (v ^ 2 * (1 - v) ^ 2 * l ^ 3)

theorem hasDerivAt_Q {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt Q (slope h) h := by
  have hv := entropyInverse_pos hh hh1.le
  have hv1 : entropyInverse h < 1 := (entropyInverse_lt_half hh.le hh1).trans (by norm_num)
  convert! (hasDerivAt_J hv hv1).comp h (hasDerivAt_entropyInverse hh hh1) using 1
  dsimp [slope]
  have hJ := J_pos hv (entropyInverse_lt_half hh.le hh1)
  field_simp [log_two_pos.ne', hv.ne', hJ.ne', show 1 - entropyInverse h ≠ 0 by linarith]

theorem hasDerivAt_slope {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt slope (curvature h) h := by
  let v := entropyInverse h
  let l := Real.log ((1 - v) / v)
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvh : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hv1 : v < 1 := by linarith
  have hJ : 0 < J v := J_pos hv hvh
  have hl : 0 < l := by
    have he : J v = l / Real.log 2 := rfl
    rw [he] at hJ
    exact (div_pos_iff_of_pos_right log_two_pos).mp hJ
  have hi := hasDerivAt_entropyInverse hh hh1
  have hd := ((hi.const_mul (Real.log 2)).mul (hi.const_sub 1)).mul
    ((hasDerivAt_J hv hv1).comp h hi)
  have hc := (hasDerivAt_const h (-1 : ℝ)).div hd (by
    change Real.log 2 * v * (1 - v) * J v ≠ 0
    positivity)
  convert! hc using 1
  dsimp only [curvature, Pi.mul_apply, Pi.sub_apply]
  change Real.log 2 * ((1 - 2 * v) * l - 1) /
      (v ^ 2 * (1 - v) ^ 2 * l ^ 3) = _
  dsimp [v, l] at *
  simp only [J]
  field_simp [log_two_pos.ne', hv.ne', hl.ne', show 1 - entropyInverse h ≠ 0 by linarith]
  ring

end GeneralCK.PsiEndpointLogGain

end


