-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailDiagonalMarginDerivative
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailDiagonalMarginDerivative
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:50:12.000478+00:00
-- url     : https://prove2.me/theorems/0fbdb282-4195-4887-97d1-93fc122e7e80
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailDiagonalMarginDerivative` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailDiagonalMarginDerivative` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailDiagonalMarginDerivative` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailDiagonalMarginDerivative (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailDiagonalMarginDerivative.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailDiagonalBias
import Definitions.Def_CK_GeneralCK_SmallMeanAnalytic

-- ===== source module GeneralCK.PureGapDoubleCapLowTailDiagonalMarginDerivative =====
section

/-! A simple exact derivative for the diagonal bias margin. It shows that
the margin increases while `biasB<3/2` and decreases afterward; endpoint
and displacement bounds are still needed for the true low-tail slope sign. -/

namespace GeneralCK

open Certificates.Reflection Reflection

noncomputable def doubleCapDiagonalMargin (y : ℝ) : ℝ :=
  (1 - y ^ 2) * SmallMean.A y * biasB y - y * biasE y

theorem doubleCapDiagonalMargin_hasDerivAt {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    HasDerivAt doubleCapDiagonalMargin
      (y * SmallMean.A y * (3 - 2 * biasB y)) y := by
  have hgap : 0 < 1 - y ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - y)
      (by linarith : 0 < 1 + y)]
  have hdgap : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * y) y := by
    have h := (((hasDerivAt_id y).pow 2).const_sub 1)
    change HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-(2 * y ^ (2 - 1) * 1)) y at h
    convert h using 1 <;> norm_num
  have hA := SmallMean.hasDerivAt_A (by linarith [hy]) hy1
  have hB := hasDerivAt_biasB (by linarith [hy]) hy1
  have hE := hasDerivAt_biasE (by linarith [hy]) hy1
  have h := ((hdgap.mul hA).mul hB).sub ((hasDerivAt_id y).mul hE)
  have heq : doubleCapDiagonalMargin =
      (fun z : ℝ => 1 - z ^ 2) * SmallMean.A * biasB - id * biasE := by
    funext z
    simp only [doubleCapDiagonalMargin, Pi.mul_apply, Pi.sub_apply, id_eq]
  rw [heq]
  convert! h using 1
  dsimp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  have hident := biasB_eq_biasE_add (by linarith [hy]) hy1
  have hcancel : (1 - y ^ 2) * (1 / (1 - y ^ 2)) = 1 := by
    field_simp [hgap.ne']
  have hcancel2 : ((1 - y ^ 2) * SmallMean.A y) *
      (y / (1 - y ^ 2)) = y * SmallMean.A y := by
    field_simp [hgap.ne']
  rw [hcancel]
  rw [hcancel2]
  nlinarith only [hident]

#print axioms doubleCapDiagonalMargin_hasDerivAt

end GeneralCK

end


