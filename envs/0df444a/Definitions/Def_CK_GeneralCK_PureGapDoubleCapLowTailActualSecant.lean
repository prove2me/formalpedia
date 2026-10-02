-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailActualSecant
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailActualSecant
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:51:01.844748+00:00
-- url     : https://prove2.me/theorems/45f72521-27ec-4a35-b8a9-2e9d384c27dc
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailActualSecant` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailActualSecant` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailActualSecant` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailActualSecant (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailActualSecant.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailUniformSecantAlgebra
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailContactLossSecant
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailLinearSeparation

-- ===== source module GeneralCK.PureGapDoubleCapLowTailActualSecant =====
section

/-! The checked high-bias anchors, inverse gap, and coupled contact
separation imply a uniform secant loss bound in the true near-zero tail. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_actual_secant_le_four_thirds {m : ℝ}
    (hm : 0 < m) (hm100 : m ≤ 1 / 100) :
    2 * ((doubleCapLowTailY m ^ 2 - doubleCapLowTailC m ^ 2) /
      ((1 - doubleCapLowTailY m ^ 2) *
       (1 - doubleCapLowTailC m ^ 2) *
       biasB (doubleCapLowTailY m))) ≤ 4 / 3 := by
  let y : ℝ := doubleCapLowTailY m
  let c : ℝ := doubleCapLowTailC m
  let k : ℝ := 1 - 2 * m
  let d : ℝ := 1 - y
  have hmq : m ≤ 1 / 4 := by linarith
  have hk : 49 / 50 ≤ k := by dsimp [k]; linarith [hm100]
  have hk0 : 0 < k := by linarith [hk]
  have hBetween0 := doubleCapLowTailC_between hm hmq
  have hBetween : k < c ∧ c < y := by
    simpa only [k, c, y] using hBetween0
  have hcHigh : 49 / 50 ≤ c := hk.trans hBetween.1.le
  have hyHigh : 49 / 50 ≤ y := hcHigh.trans hBetween.2.le
  have hc0 : 0 < c := by linarith [hcHigh]
  have hy0 : 0 < y := by linarith [hyHigh]
  have hcy : c ≤ y := hBetween.2.le
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : y < 1 := by
    dsimp [y, doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hc1 : c < 1 := hcy.trans_lt hy1
  have hd : 0 < d := by dsimp [d]; linarith [hy1]
  have hmd : m ≤ d := by
    dsimp [d, y]
    linarith [doubleCapLowTailY_le_one_sub_m hm (by linarith : m ≤ 1 / 8)]
  have hp : 99 / 50 ≤ 1 + y := by linarith [hyHigh]
  have hq : 99 / 50 ≤ 1 + c := by linarith [hcHigh]
  have hBc := doubleCapLowTail_B_ge_207 hcHigh hc1
  have hBc0 : 0 < biasB c := by linarith [hBc]
  have hBy0 : 0 < biasB y := by
    linarith [doubleCapLowTail_B_ge_207 hyHigh hy1]
  have hE := doubleCapLowTail_E_le_five_fourths_gap_B hyHigh hy1
  have hDy : 0 < 1 - y ^ 2 := by nlinarith
  have hDc : 0 < 1 - c ^ 2 := by nlinarith
  have hDenSep : 0 < k ^ 2 * biasB c :=
    mul_pos (sq_pos_of_pos hk0) hBc0
  have hSep0 : y - c ≤
      (2 * m * c ^ 2 * biasE y) / (k ^ 2 * biasB c) := by
    simpa only [y, c, k] using doubleCapLowTail_bias_separation_linear hm hmq
  have hSepCross : (y - c) * k ^ 2 * biasB c ≤
      2 * m * c ^ 2 * biasE y := by
    have h := (le_div_iff₀ hDenSep).mp hSep0
    nlinarith only [h]
  have hcSq : c ^ 2 ≤ 1 := by nlinarith [hc1]
  have hScaleE := mul_le_mul_of_nonneg_left hE
    (mul_nonneg (by linarith : 0 ≤ 2 * m) (sq_nonneg c))
  have hScaleSq := mul_le_mul_of_nonneg_left hcSq
    (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (5 / 2) * m) hd.le) hBy0.le)
  have hSepUpper : (y - c) * k ^ 2 * biasB c ≤
      (5 / 2) * m * d * biasB y := by
    dsimp [d] at hScaleE hScaleSq
    nlinarith only [hSepCross, hScaleE, hScaleSq]
  have hDcLower : d * (1 + c) ≤ 1 - c ^ 2 := by
    have hcGap : d ≤ 1 - c := by dsimp [d]; linarith [hcy]
    have h := mul_le_mul_of_nonneg_right hcGap (by linarith : 0 ≤ 1 + c)
    dsimp [d] at h ⊢
    nlinarith only [h]
  have hDyEq : 1 - y ^ 2 = d * (1 + y) := by dsimp [d]; ring
  have hDenMid : d ^ 2 * (1 + y) * (1 + c) ≤
      (1 - y ^ 2) * (1 - c ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hDcLower hDy.le
    rw [hDyEq] at h
    nlinarith only [h]
  have hDenLower : d ^ 2 * (1 + y) * (1 + c) * biasB y ≤
      (1 - y ^ 2) * (1 - c ^ 2) * biasB y := by
    have h := mul_le_mul_of_nonneg_right hDenMid hBy0.le
    nlinarith only [h]
  have hDen : 0 < (1 - y ^ 2) * (1 - c ^ 2) * biasB y :=
    mul_pos (mul_pos hDy hDc) hBy0
  have hδ : 0 ≤ y - c := sub_nonneg.mpr hcy
  have hAbstract := doubleCapLowTail_uniform_secant_abstract
    hm hd hmd hk hBc hp hq hBy0 hDen hδ hSepUpper hDenLower
  have hSquareUpper : y ^ 2 - c ^ 2 ≤ 2 * (y - c) := by
    have hPlus : y + c ≤ 2 := by linarith [hy1, hc1]
    have h := mul_le_mul_of_nonneg_left hPlus hδ
    nlinarith only [h]
  have hNum : 2 * (y ^ 2 - c ^ 2) ≤ 4 * (y - c) := by
    linarith only [hSquareUpper]
  have hFraction : (2 * (y ^ 2 - c ^ 2)) /
      ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) ≤
      4 * (y - c) /
        ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) :=
    (div_le_div_iff₀ hDen hDen).mpr
      (mul_le_mul_of_nonneg_right hNum hDen.le)
  calc
    2 * ((doubleCapLowTailY m ^ 2 - doubleCapLowTailC m ^ 2) /
        ((1 - doubleCapLowTailY m ^ 2) *
         (1 - doubleCapLowTailC m ^ 2) *
         biasB (doubleCapLowTailY m))) =
        (2 * (y ^ 2 - c ^ 2)) /
          ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) := by ring
    _ ≤ 4 * (y - c) /
          ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) := hFraction
    _ ≤ 4 / 3 := hAbstract

#print axioms doubleCapLowTail_actual_secant_le_four_thirds

end GeneralCK

end


