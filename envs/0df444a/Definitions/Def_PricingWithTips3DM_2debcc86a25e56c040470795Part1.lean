-- Prove2me | Definitions.Def_PricingWithTips3DM_2debcc86a25e56c040470795Part1
-- name    : PricingWithTips3DM_2debcc86a25e56c040470795Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:11:41.888562+00:00
-- url     : https://prove2.me/theorems/3a0a5080-9c1c-4c28-b4f6-162a62c509e4
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeStructuralCandidatesTM2.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_68d8756d3d1b4518f6d0de29
import Definitions.Def_PricingWithTips3DM_2228fa1d1515c33116147ff5
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! A second certificate with exactly the same position layout as the tagged
key certificate.  Clause positions carry their ordinal contribution and
literal positions carry their block base, so every cross-section raw pair is
the corresponding literal-test cell ordinal by endpoint addition. -/

noncomputable section

namespace PricingWithTips.FixedShapeStructuralCandidatesTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open _root_.Turing
open PricingWithTips.FixedShapeLiteralCandidatesTM2
open PricingWithTips.FixedShapeLiteralOrdinalArithmetic

def clauseFrames (input : List CNFSym) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    0 clauseStridePolynomial lengthPolynomial input

def negativeBaseFrames (input : List CNFSym) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    negativeBasePolynomial variableStridePolynomial lengthPolynomial input

def positiveBaseFrames (input : List CNFSym) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    positiveBasePolynomial variableStridePolynomial lengthPolynomial input

noncomputable def clauseFrames_computableInPolyTime :
    TM2ComputableInPolyTime id id clauseFrames :=
  exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (Γ := CNFSym) 0 clauseStridePolynomial lengthPolynomial

noncomputable def negativeBaseFrames_computableInPolyTime :
    TM2ComputableInPolyTime id id negativeBaseFrames :=
  exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (Γ := CNFSym) negativeBasePolynomial variableStridePolynomial
      lengthPolynomial

noncomputable def positiveBaseFrames_computableInPolyTime :
    TM2ComputableInPolyTime id id positiveBaseFrames :=
  exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (Γ := CNFSym) positiveBasePolynomial variableStridePolynomial
      lengthPolynomial

def clauseRecords (input : List CNFSym) : List CliqueSym :=
  vertexRecordFormatter (clauseFrames input)

def negativeBaseRecords (input : List CNFSym) : List CliqueSym :=
  vertexRecordFormatter (negativeBaseFrames input)

def positiveBaseRecords (input : List CNFSym) : List CliqueSym :=
  vertexRecordFormatter (positiveBaseFrames input)

noncomputable def clauseRecords_computableInPolyTime :
    TM2ComputableInPolyTime id id clauseRecords :=
  Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    clauseFrames_computableInPolyTime
    vertexRecordFormatter_computableInPolyTime)

noncomputable def negativeBaseRecords_computableInPolyTime :
    TM2ComputableInPolyTime id id negativeBaseRecords :=
  Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    negativeBaseFrames_computableInPolyTime
    vertexRecordFormatter_computableInPolyTime)

noncomputable def positiveBaseRecords_computableInPolyTime :
    TM2ComputableInPolyTime id id positiveBaseRecords :=
  Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    positiveBaseFrames_computableInPolyTime
    vertexRecordFormatter_computableInPolyTime)

def literalBaseRecords (input : List CNFSym) : List CliqueSym :=
  negativeBaseRecords input ++ positiveBaseRecords input

noncomputable def literalBaseRecords_computableInPolyTime :
    TM2ComputableInPolyTime id id literalBaseRecords :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    negativeBaseRecords_computableInPolyTime
    positiveBaseRecords_computableInPolyTime

def structuralBody (input : List CNFSym) : List CliqueSym :=
  clauseRecords input ++ literalBaseRecords input

noncomputable def structuralBody_computableInPolyTime :
    TM2ComputableInPolyTime id id structuralBody :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    clauseRecords_computableInPolyTime literalBaseRecords_computableInPolyTime

def structuralVertices (input : List CNFSym) : List Nat :=
  (List.range input.length).map (clauseContribution input.length) ++
    (List.range input.length).map
      (fun v => literalBase input.length v false) ++
    (List.range input.length).map
      (fun v => literalBase input.length v true)
end PricingWithTips.FixedShapeStructuralCandidatesTM2


