-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeIdentity
-- name    : CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeIdentity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:41:26.099066+00:00
-- url     : https://prove2.me/theorems/234067f9-ab46-4974-abac-06d29380f144
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeIdentity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeIdentity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeIdentity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighMiddleDerivativeIdentity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighMiddleDerivativeIdentity.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeChecker
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural

-- ===== source module GeneralCK.PureGapDoubleCapHighMiddleDerivativeIdentity =====
section

/-! Source draft for the exact true high-cap slope derivative identity.
The two implicit y/c derivative adapters remain explicit premises until
their compositions from checked entropyInverse/regularContact lemmas compile.
No numerical interval output enters these calculus lemmas. -/

namespace GeneralCK
open Certificates.Reflection

private theorem hasDerivAt_doubleCapNegativeBiasTerm {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt
      (fun q : ℝ => 2 - 2 * q / ((1 - q ^ 2) * SmallMean.A q))
      (-2 * (((1 + z ^ 2) * SmallMean.A z - z) /
        (((1 - z ^ 2) * SmallMean.A z) ^ 2))) z := by
  have hgap : 0 < 1 - z ^ 2 := by nlinarith [hz0, hz1]
  have hA : 0 < SmallMean.A z := by
    linarith [SmallMean.A_lower hz0.le hz1]
  have hD : (1 - z ^ 2) * SmallMean.A z ≠ 0 :=
    (mul_pos hgap hA).ne'
  have hGap := ((hasDerivAt_id z).pow 2).const_sub 1
  have hAD := SmallMean.hasDerivAt_A (by linarith : -1 < z) hz1
  have hDen := hGap.mul hAD
  have hDiv := (hasDerivAt_id z).div hDen hD
  have hRaw := (hasDerivAt_const z (2 : ℝ)).sub (hDiv.const_mul 2)
  convert! hRaw using 1
  · funext q
    dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
    ring
  · dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
    field_simp [hD, hgap.ne', hA.ne']
    ring

private theorem hasDerivAt_doubleCapPositiveBiasTerm {z : ℝ}
    (hz0 : -1 < z) (hz1 : z < 1) :
    HasDerivAt
      (fun q : ℝ => 2 * q ^ 2 / ((1 - q ^ 2) * biasB q))
      (2 * (z * (2 * biasB z - z ^ 2) /
        (((1 - z ^ 2) * biasB z) ^ 2))) z := by
  have hgap : 0 < 1 - z ^ 2 := by nlinarith [hz0, hz1]
  have hB : 0 < biasB z := Reflection.biasB_pos_wide hz0 hz1
  have hD : (1 - z ^ 2) * biasB z ≠ 0 :=
    (mul_pos hgap hB).ne'
  have hGap := ((hasDerivAt_id z).pow 2).const_sub 1
  have hBD := Reflection.hasDerivAt_biasB hz0 hz1
  have hDen := hGap.mul hBD
  have hDiv := ((hasDerivAt_id z).pow 2).div hDen hD
  have hRaw := hDiv.const_mul 2
  convert! hRaw using 1
  · funext q
    dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
    ring
  · dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
    field_simp [hD, hgap.ne', hB.ne']
    ring

/-- Exact calculus identity assuming only the two true implicit derivative
adapters. The adapter conclusions are stated as `HasDerivAt` premises, not
axioms; separate Lean theorems must derive them from checked primitives. -/
theorem doubleCapBridgeSlope_hasDerivAt_of_implicit
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ))
    (hY : HasDerivAt doubleCapHighTailY
      (SmallMean.A (2 * x) / SmallMean.A (doubleCapHighTailY x)) x)
    (hC : HasDerivAt doubleCapHighTailC
      ((biasE (doubleCapHighTailC x) +
          doubleCapHighTailC x * SmallMean.A (2 * x)) /
        (doubleCapBridgeL x +
          x * SmallMean.A (doubleCapHighTailC x))) x) :
    HasDerivAt doubleCapBridgeSlope
      (doubleCapBridgeDerivativeExpression x) x := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 / 2 := by linarith [hx.2]
  have hh : 0 < doubleCapHighTailFloor x :=
    doubleCapHighTailFloor_pos hx0 hx1
  have hh1 : doubleCapHighTailFloor x < 1 := by
    have hfloor := doubleCapHighFloor_lt_entropyCap
      (m := (1 - x) / 2) (by linarith) (by linarith)
    have hH1 := H_le_one ((1 - x) / 2)
    unfold doubleCapHighTailFloor
    have heq : 2 * ((1 - x) / 2) - 1 / 2 = (1 - 2 * x) / 2 := by ring
    rw [heq] at hfloor
    linarith
  have hy0 : 0 < doubleCapHighTailY x := by
    unfold doubleCapHighTailY
    linarith [entropyInverse_lt_half hh.le hh1]
  have hy1 : doubleCapHighTailY x < 1 := by
    unfold doubleCapHighTailY
    linarith [entropyInverse_pos hh hh1.le]
  have hmem := Reflection.regularContact_mem
    (x / (Real.log 2 * doubleCapHighTailFloor x))
  have hc0 : -1 < doubleCapHighTailC x := hmem.1
  have hc1 : doubleCapHighTailC x < 1 := hmem.2
  have hNeg := (hasDerivAt_doubleCapNegativeBiasTerm hy0 hy1).comp x hY
  have hPos := (hasDerivAt_doubleCapPositiveBiasTerm hc0 hc1).comp x hC
  have hSum := hNeg.add hPos
  convert! hSum using 1

#print axioms doubleCapBridgeSlope_hasDerivAt_of_implicit

end GeneralCK

end


