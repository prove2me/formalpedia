-- Prove2me | Definitions.Def_PricingWithTips3DM_d3580fa66ff8cd5440556f0f
-- name    : PricingWithTips3DM_d3580fa66ff8cd5440556f0f
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T12:58:32.443065+00:00
-- url     : https://prove2.me/theorems/99b33982-981a-4a23-8777-eb63debfe653
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeReductionTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_401d020bee71a0b59916e88f
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! The complete native TM2 computing the fixed-shape SAT-to-3DM encoding. -/

noncomputable section

namespace PricingWithTips.FixedShapeReductionTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing.PolyBuilder
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeEncoding
open PricingWithTips.FixedShapeBaselineTM2
open PricingWithTips.FixedShapeDenseTableTM2
open PricingWithTips.FixedShapeDenseTableSemantics

def encodedReduction (input : List CNFSym) : List Bool :=
  prefixBits input ++ denseBits input

theorem encodedReduction_eq (input : List CNFSym) :
    encodedReduction input = encodeThreeDMInstance (reduction input) := by
  rw [encodedReduction, prefixBits_eq, denseBits_eq_table,
    encode_reduction_eq]

noncomputable def encodedReduction_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id encodedReduction :=
  fixedPairSameInputConcat_computableInPolyTime
    boolPairEncode boolPairDecode boolPair_leftInverse
    (by
      let frames :=
        exactPolynomialUnaryFrame_computableInPolyTime
          (Γ := CNFSym) dimensionPolynomial
      exact Classical.choice (Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
        frames (boundedLoop_computableInPolyTime prefixBitBody)))
    denseBits_computableInPolyTime

noncomputable def reduction_computableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (id : List CNFSym → List CNFSym)
      encodeThreeDMInstance reduction := by
  let machine := encodedReduction_computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [encodedReduction_eq] using output }

theorem threeDM_np_hard : NPHardMarketPredicate ThreeDMYes :=
  FixedShape3DM.threeDM_np_hard_of_reduction_polytime
    ⟨reduction_computableInPolyTime⟩

end PricingWithTips.FixedShapeReductionTM2


