-- Prove2me | Definitions.Def_PricingWithTips3DM_8169be64da1591889851249c
-- name    : PricingWithTips3DM_8169be64da1591889851249c
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:46:20.047093+00:00
-- url     : https://prove2.me/theorems/9c1622cf-131f-411b-a153-44687d78e031
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_efa956dc2c0c600e413bcbbc
import Definitions.Def_PricingWithTips3DM_693ce23dec6dc45ed34c4fb1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Same-input concatenation through a fixed pair codec

The existing parallel concatenator works over `UnaryFrameSym`.  A fixed
two-symbol left-invertible code transports that closure theorem to any finite
alphabet admitting such a code.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Two same-input transducers can be concatenated after transporting their
output alphabet through a fixed pair code over `UnaryFrameSym`. -/
noncomputable def fixedPairSameInputConcat_computableInPolyTime
    {α Γ Ω : Type} [Fintype Γ] [Fintype Ω]
    {inputEncoding : α → List Γ}
    (encode : Ω → UnaryFrameSym × UnaryFrameSym)
    (decode : UnaryFrameSym → UnaryFrameSym → Ω)
    (hleft : ∀ symbol, decode (encode symbol).1 (encode symbol).2 = symbol)
    {left right : α → List Ω}
    (M₁ : _root_.Turing.TM2ComputableInPolyTime inputEncoding id left)
    (M₂ : _root_.Turing.TM2ComputableInPolyTime inputEncoding id right) :
    _root_.Turing.TM2ComputableInPolyTime inputEncoding id
      (fun input => left input ++ right input) := by
  let encoder := fixedPairEncode_computableInPolyTime encode
  let leftEncodedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch M₁ encoder
  let rightEncodedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch M₂ encoder
  let leftEncoded := Classical.choice leftEncodedExists
  let rightEncoded := Classical.choice rightEncodedExists
  let joined := unaryFrameSameInputConcat_computableInPolyTime
    leftEncoded rightEncoded
  let decodedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch joined
      (fixedPairDecode_computableInPolyTime decode)
  let decoded := Classical.choice decodedExists
  exact
    { tm := decoded.tm
      inputAlphabet := decoded.inputAlphabet
      outputAlphabet := decoded.outputAlphabet
      time := decoded.time
      outputsFun := fun input => by
        have run := decoded.outputsFun input
        have hsemantic :
            fixedPairDecode decode
                (fixedPairEncode encode (left input) ++
                  fixedPairEncode encode (right input)) =
              left input ++ right input := by
          rw [← fixedPairEncode_append]
          exact fixedPairDecode_encode encode decode hleft
            (left input ++ right input)
        simp only [Function.comp_def, id_eq] at run
        rw [hsemantic] at run
        simpa only [Function.comp_def, id_eq] using run }

end CLRS.Chapter34.Turing.PolyBuilder


