-- Prove2me | Definitions.Def_PricingWithTips3DM_0a86702738a5c2a52d5525ca
-- name    : PricingWithTips3DM_0a86702738a5c2a52d5525ca
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:43:30.884909+00:00
-- url     : https://prove2.me/theorems/d6b88c11-f797-44ac-8950-dec8e3aebe61
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeDenseTableTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_a08d30f6b66a2a276a87ce8f
import Definitions.Def_PricingWithTips3DM_4e826b46f3c1a426fe602561
import Definitions.Def_PricingWithTips3DM_cab083267a7384abeae850b3
import Definitions.Def_PricingWithTips3DM_a93140320b2ce04366c96818
import Definitions.Def_PricingWithTips3DM_67cd49331ca6f872d03ef334
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Assemble every sparse true-cell family and run the verified batch lookup
against the complete dense ordinal query stream. -/

noncomputable section

namespace PricingWithTips.FixedShapeDenseTableTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open _root_.Turing
open PricingWithTips.FixedShapeClauseMembershipTM2
open PricingWithTips.FixedShapeQueryStream
open PricingWithTips.FixedShapeTrueEdgesTM2
open PricingWithTips.FixedShapeFalseEdgesTM2
open PricingWithTips.FixedShapeJunkEdgesTM2
open PricingWithTips.FixedShapeLiteralSelectorTM2

def fixedSparseStream (input : List CNFSym) : List CliqueSym :=
  trueEdgeStream input ++ falseEdgeStream input ++ junkEdgeStream input

noncomputable def trueFalseStream_computableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun input => trueEdgeStream input ++ falseEdgeStream input) :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    PricingWithTips.FixedShapeTrueEdgesTM2.computableInPolyTime
    falseEdgeStream_computableInPolyTime

noncomputable def fixedSparseStream_computableInPolyTime :
    TM2ComputableInPolyTime id id fixedSparseStream :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    trueFalseStream_computableInPolyTime junkEdgeStream_computableInPolyTime

def allSparseStream (input : List CNFSym) : List CliqueSym :=
  fixedSparseStream input ++ literalEdgeStream input

noncomputable def allSparseStream_computableInPolyTime :
    TM2ComputableInPolyTime id id allSparseStream :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    fixedSparseStream_computableInPolyTime
    literalEdgeStream_computableInPolyTime

def generatedEdges (input : List CNFSym) : List (Nat × Nat) :=
  trueEdges input ++ falseEdges input ++ junkEdges input ++ literalEdges input

theorem allSparseStream_eq (input : List CNFSym) :
    allSparseStream input =
      (generatedEdges input).flatMap encodeCliqueEdge := by
  simp [allSparseStream, fixedSparseStream, generatedEdges,
    trueEdgeStream_eq, falseEdgeStream_eq, junkEdgeStream_eq,
    literalEdgeStream_eq, List.flatMap_append, List.append_assoc]

def generatedInstance (input : List CNFSym) : CliqueInstance where
  vertexCount := 0
  targetSize := 0
  edges := generatedEdges input

def graphStream (input : List CNFSym) : List CliqueSym :=
  encodeCliqueInstance (generatedInstance input)

theorem graphStream_eq (input : List CNFSym) :
    graphStream input = emptyHeader input ++ allSparseStream input := by
  rw [emptyHeader_eq, allSparseStream_eq]
  simp [graphStream, generatedInstance, encodeCliqueInstance,
    prependCliqueTicks]

noncomputable def graphStream_computableInPolyTime :
    TM2ComputableInPolyTime id id graphStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    emptyHeader_computableInPolyTime allSparseStream_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [← graphStream_eq input] at output
        exact output }

def queryPairLeft (input : List CNFSym) : List (Option CliqueSym) :=
  OptionPairLeft.format (queryStream input)

def graphPairRight (input : List CNFSym) : List (Option CliqueSym) :=
  (graphStream input).map some

noncomputable def queryPairLeft_computableInPolyTime :
    TM2ComputableInPolyTime id id queryPairLeft :=
  Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    PricingWithTips.FixedShapeQueryStream.computableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym))

noncomputable def graphPairRight_computableInPolyTime :
    TM2ComputableInPolyTime id id graphPairRight :=
  Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    graphStream_computableInPolyTime
    (someMap_computableInPolyTime CliqueSym))

def batchInput (input : List CNFSym) :
    List (Nat × Nat) × CliqueInstance :=
  (queries input, generatedInstance input)

noncomputable def batchInput_computableInPolyTime :
    TM2ComputableInPolyTime id
      (fun pr : List (Nat × Nat) × CliqueInstance =>
        pairEncoding (pr.1.flatMap encodeCliqueEdge)
          (encodeCliqueInstance pr.2)) batchInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    PricingWithTips.FixedShapeClauseMembershipTM2.encodeOptionCliqueSymPair
    PricingWithTips.FixedShapeClauseMembershipTM2.decodeOptionCliqueSymPair
    PricingWithTips.FixedShapeClauseMembershipTM2.decode_encodeOptionCliqueSymPair
    queryPairLeft_computableInPolyTime graphPairRight_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [batchInput, queryPairLeft, graphPairRight, pairEncoding,
          OptionPairLeft.format, queryStream_eq, graphStream,
          List.append_assoc] using output }

def lookupResults (input : List CNFSym) : List Bool :=
  BatchEdgeLookup.batchResultStream
    (generatedInstance input) (queries input)

noncomputable def lookupResults_computableInPolyTime :
    TM2ComputableInPolyTime id id lookupResults := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchInput_computableInPolyTime BatchEdgeLookup.batchResultsComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => BatchEdgeLookup.batchResultStream
      (generatedInstance input) (queries input))
  simpa only [Function.comp_def, batchInput] using Classical.choice composed

def denseBits (input : List CNFSym) : List Bool :=
  (queries input).map fun edge => decide (edge ∈ (generatedInstance input).edges)

theorem dropHead_lookupResults (input : List CNFSym) :
    DropHead.stream (lookupResults input) = denseBits input := by
  simp [lookupResults, BatchEdgeLookup.batchResultStream,
    BatchEdgeLookup.queryMembershipBits, denseBits, DropHead.stream]

noncomputable def denseBits_computableInPolyTime :
    TM2ComputableInPolyTime id id denseBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    lookupResults_computableInPolyTime (DropHead.computableInPolyTime Bool)
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [Function.comp_def, dropHead_lookupResults] using output }

end PricingWithTips.FixedShapeDenseTableTM2


