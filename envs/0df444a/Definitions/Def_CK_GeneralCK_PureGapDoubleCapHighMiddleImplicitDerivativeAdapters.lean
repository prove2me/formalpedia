-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleImplicitDerivativeAdapters
-- name    : CK_GeneralCK_PureGapDoubleCapHighMiddleImplicitDerivativeAdapters
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:48:22.53676+00:00
-- url     : https://prove2.me/theorems/ae728c0a-8ecd-4c5d-a2c5-595bf4e222c3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighMiddleImplicitDerivativeAdapters` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighMiddleImplicitDerivativeAdapters` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighMiddleImplicitDerivativeAdapters` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighMiddleImplicitDerivativeAdapters (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighMiddleImplicitDerivativeAdapters.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeIdentity
import Definitions.Def_CK_GeneralCK_EntropyComparison

-- ===== source module GeneralCK.PureGapDoubleCapHighMiddleImplicitDerivativeAdapters =====
section

/-! Source draft: true implicit y/c derivatives needed by the 256-cell
high-middle slope checker. No numerical witness is used as a premise.
All four named theorems require local Lean compilation and audit. -/

namespace GeneralCK
open Certificates.Reflection

theorem doubleCapBridgeL_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    HasDerivAt doubleCapBridgeL (-SmallMean.A (2 * x)) x := by
  have hFn : doubleCapBridgeL =
      (fun z : ℝ => Real.log 2 - SmallMean.Cn (2 * z) / 2) := by
    funext z
    unfold doubleCapBridgeL doubleCapHighTailFloor SmallMean.Cn
    ring
  rw [hFn]
  have hA := SmallMean.hasDerivAt_Cn
    (show -1 < 2 * x by linarith [hx.1])
    (show 2 * x < 1 by linarith [hx.2])
  have hInner : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hRaw := ((hA.comp x hInner).div_const 2).const_sub (Real.log 2)
  convert! hRaw using 1
  ring

theorem doubleCapHighTailY_hasDerivAt_implicit {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    HasDerivAt doubleCapHighTailY
      (SmallMean.A (2 * x) / SmallMean.A (doubleCapHighTailY x)) x := by
  let p : ℝ := (1 - 2 * x) / 2
  let h : ℝ := doubleCapHighTailFloor x
  let v : ℝ := entropyInverse h
  have hp0 : 0 < p := by dsimp [p]; linarith [hx.2]
  have hp1 : p < 1 := by dsimp [p]; linarith [hx.1]
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 / 2 := by linarith [hx.2]
  have hh0 : 0 < h := doubleCapHighTailFloor_pos hx0 hx1
  have hh1 : h < 1 := by
    have hfloor := doubleCapHighFloor_lt_entropyCap
      (m := (1 - x) / 2) (by linarith) (by linarith)
    have hH1 := H_le_one ((1 - x) / 2)
    dsimp [h, doubleCapHighTailFloor]
    have heq : 2 * ((1 - x) / 2) - 1 / 2 = (1 - 2 * x) / 2 := by ring
    rw [heq] at hfloor
    linarith
  have hv0 : 0 < v := entropyInverse_pos hh0 hh1.le
  have hvh : v < 1 / 2 := entropyInverse_lt_half hh0.le hh1
  have hJv : 0 < J v := J_pos hv0 hvh
  have hP : HasDerivAt (fun z : ℝ => (1 - 2 * z) / 2) (-1) x := by
    have hRaw := (((hasDerivAt_id x).const_mul 2).const_sub 1).div_const 2
    convert! hRaw using 1
    ring
  have hH := (Comparison.hasDerivAt_H hp0 hp1).comp x hP
  have hFloor : HasDerivAt doubleCapHighTailFloor (-J p / 2) x := by
    have hRaw := ((hasDerivAt_const x (1 : ℝ)).add hH).div_const 2
    convert! hRaw using 1
    ring
  have hInv := (hasDerivAt_entropyInverse hh0 hh1).comp x hFloor
  have hYraw := (hasDerivAt_const x (1 : ℝ)).sub (hInv.const_mul 2)
  have hy0 : 0 < doubleCapHighTailY x := by
    dsimp [doubleCapHighTailY, v, h]
    linarith [hvh]
  have hy1 : doubleCapHighTailY x < 1 := by
    dsimp [doubleCapHighTailY, v, h]
    linarith [hv0]
  have hAy : 0 < SmallMean.A (doubleCapHighTailY x) := by
    linarith [SmallMean.A_lower hy0.le hy1]
  have hA2 := Correction.Natural.A_probability p
  have hAv := Correction.Natural.A_probability v
  have hPId : 1 - 2 * p = 2 * x := by dsimp [p]; ring
  have hVId : 1 - 2 * v = doubleCapHighTailY x := rfl
  rw [hPId] at hA2
  rw [hVId] at hAv
  have hRatioCross :
      SmallMean.A (2 * x) * J v =
        J p * SmallMean.A (doubleCapHighTailY x) := by
    linear_combination (J v / 2) * hA2 - (J p / 2) * hAv
  have hRatio :
      SmallMean.A (2 * x) / SmallMean.A (doubleCapHighTailY x) =
        J p / J v :=
    (div_eq_div_iff hAy.ne' hJv.ne').2 (by nlinarith [hRatioCross])
  convert! hYraw using 1
  rw [hRatio]
  change J p / J v = 0 - 2 * (1 / J v * (-J p / 2))
  field_simp [hJv.ne']
  ring

theorem doubleCapHighTailC_hasDerivAt_implicit {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    HasDerivAt doubleCapHighTailC
      ((biasE (doubleCapHighTailC x) +
          doubleCapHighTailC x * SmallMean.A (2 * x)) /
        (doubleCapBridgeL x +
          x * SmallMean.A (doubleCapHighTailC x))) x := by
  let l : ℝ := doubleCapBridgeL x
  let c : ℝ := doubleCapHighTailC x
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 / 2 := by linarith [hx.2]
  have hl : 0 < l := mul_pos log_two_pos
    (doubleCapHighTailFloor_pos hx0 hx1)
  have hmem := Reflection.regularContact_mem (x / l)
  have hcMem : -1 < c ∧ c < 1 := hmem
  have he : 0 < biasE c := Reflection.biasE_pos_wide hcMem.1 hcMem.2
  have hb : 0 < biasB c := Reflection.biasB_pos_wide hcMem.1 hcMem.2
  have hCross : c * l = x * biasE c := by
    have hEq := doubleCapHighTailC_equation x
    change c = (x / l) * biasE c at hEq
    field_simp [hl.ne'] at hEq
    nlinarith [hEq]
  have hBidentity : biasB c = biasE c + c * SmallMean.A c :=
    Reflection.biasB_eq_biasE_add hcMem.1 hcMem.2
  have hNumEq :
      (biasE c + c * SmallMean.A (2 * x)) * l =
        biasE c * (l + x * SmallMean.A (2 * x)) := by
    linear_combination SmallMean.A (2 * x) * hCross
  have hDenEq :
      biasE c * (l + x * SmallMean.A c) = l * biasB c := by
    linear_combination -(SmallMean.A c) * hCross - l * hBidentity
  have hLderiv := doubleCapBridgeL_hasDerivAt hx
  have hTau := (hasDerivAt_id x).div hLderiv hl.ne'
  have hContact :=
    (Reflection.hasDerivAt_regularContact (x / l)).comp x hTau
  have hden : l + x * SmallMean.A c ≠ 0 := by
    have hc0 : 0 < c := by
      have hm := mul_pos hx0 he
      nlinarith [hCross, hl]
    have hAc : 0 < SmallMean.A c := by
      linarith [SmallMean.A_lower hc0.le hcMem.2]
    exact (add_pos_of_pos_of_nonneg hl
      (mul_nonneg hx0.le hAc.le)).ne'
  convert! hContact using 1
  have hcEq : Reflection.regularContact (x / l) = c := rfl
  rw [hcEq]
  simp only [id_eq, one_mul]
  have hCDef : doubleCapHighTailC x = c := rfl
  have hLDef : doubleCapBridgeL x = l := rfl
  rw [hCDef, hLDef]
  rw [show l - x * (-SmallMean.A (2 * x)) =
      l + x * SmallMean.A (2 * x) by ring]
  change (biasE c + c * SmallMean.A (2 * x)) /
      (l + x * SmallMean.A c) =
    biasE c ^ 2 / biasB c * ((l + x * SmallMean.A (2 * x)) / l ^ 2)
  field_simp [hl.ne', he.ne', hb.ne', hden]
  linear_combination (l * biasB c) * hNumEq -
    (biasE c * (l + x * SmallMean.A (2 * x))) * hDenEq

theorem doubleCapBridgeSlope_hasDerivAt_on_high_middle {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    HasDerivAt doubleCapBridgeSlope
      (doubleCapBridgeDerivativeExpression x) x :=
  doubleCapBridgeSlope_hasDerivAt_of_implicit hx
    (doubleCapHighTailY_hasDerivAt_implicit hx)
    (doubleCapHighTailC_hasDerivAt_implicit hx)

#print axioms doubleCapBridgeL_hasDerivAt
#print axioms doubleCapHighTailY_hasDerivAt_implicit
#print axioms doubleCapHighTailC_hasDerivAt_implicit
#print axioms doubleCapBridgeSlope_hasDerivAt_on_high_middle

end GeneralCK

end


