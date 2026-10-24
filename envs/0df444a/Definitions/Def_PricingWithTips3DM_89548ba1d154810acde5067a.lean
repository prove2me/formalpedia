-- Prove2me | Definitions.Def_PricingWithTips3DM_89548ba1d154810acde5067a
-- name    : PricingWithTips3DM_89548ba1d154810acde5067a
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:03:31.919898+00:00
-- url     : https://prove2.me/theorems/ffd69e76-b928-4993-8a51-718a5b710509
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeLiteralMembershipTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_cb48696a231cc5a8706d50c4
import Definitions.Def_PricingWithTips3DM_68d8756d3d1b4518f6d0de29
import Definitions.Def_PricingWithTips3DM_a0b3f1a7d600b0df4bcc86f8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Batch lookup of every tagged certificate pair against the complete sparse
literal-key table (guarded base occurrences plus selected padding literals).
Same-section pairs are absent automatically by parity. -/

noncomputable section

namespace PricingWithTips.FixedShapeLiteralMembershipTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
open _root_.Turing
open PricingWithTips.FixedShapeClauseMembershipTM2
open PricingWithTips.FixedShapeGuardedKeysTM2
open PricingWithTips.FixedShapeTaggedKeysTM2
open PricingWithTips.FixedShapeLiteralCandidatesTM2
open PricingWithTips.FixedShapePaddingSelectorTM2

def taggedPaddingKeyStream (input : List CNFSym) : List CliqueSym :=
  tagKeyStream (selectedPaddingStream input)

noncomputable def taggedPaddingKeyStream_computableInPolyTime :
    TM2ComputableInPolyTime id id taggedPaddingKeyStream :=
  Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    selectedPaddingStream_computableInPolyTime
    tagKeyStream_computableInPolyTime)

def allTaggedKeyStream (input : List CNFSym) : List CliqueSym :=
  taggedGuardedBaseKeyStream input ++ taggedPaddingKeyStream input

noncomputable def allTaggedKeyStream_computableInPolyTime :
    TM2ComputableInPolyTime id id allTaggedKeyStream :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    taggedGuardedBaseKeyStream_computableInPolyTime
    taggedPaddingKeyStream_computableInPolyTime

def selectedPaddingEdges (input : List CNFSym) : List (Nat × Nat) :=
  Selector.alignedSelectedEdges
    (PricingWithTips.FixedShapePaddingSelectorTM2.alignedInput input)

theorem selectedPaddingStream_eq (input : List CNFSym) :
    selectedPaddingStream input =
      (selectedPaddingEdges input).flatMap encodeCliqueEdge := by
  rfl

def taggedKey (key : Nat × Nat) : Nat × Nat :=
  (2 * key.1, 2 * key.2 + 1)

def allTaggedKeys (input : List CNFSym) : List (Nat × Nat) :=
  (PricingWithTips.FixedShapeLiteralKeySemantics.guardedCanonicalKeys input).map
      taggedKey ++
    (selectedPaddingEdges input).map taggedKey

theorem allTaggedKeyStream_eq (input : List CNFSym) :
    allTaggedKeyStream input =
      (allTaggedKeys input).flatMap encodeCliqueEdge := by
  simp only [allTaggedKeyStream, taggedGuardedBaseKeyStream,
    taggedPaddingKeyStream, selectedPaddingStream_eq,
    PricingWithTips.FixedShapeGuardedKeysTM2.guardedBaseKeyStream,
    tag_keys, List.flatMap_append, List.flatMap_map]
  simp [allTaggedKeys, taggedKey, List.flatMap_append,
    List.flatMap_map, Function.comp_def]

def literalKeyInstance (input : List CNFSym) : CliqueInstance where
  vertexCount := 0
  targetSize := 0
  edges := allTaggedKeys input

def literalKeyGraphStream (input : List CNFSym) : List CliqueSym :=
  encodeCliqueInstance (literalKeyInstance input)

theorem literalKeyGraphStream_eq (input : List CNFSym) :
    literalKeyGraphStream input = emptyHeader input ++ allTaggedKeyStream input := by
  rw [emptyHeader_eq, allTaggedKeyStream_eq]
  simp [literalKeyGraphStream, literalKeyInstance, encodeCliqueInstance,
    prependCliqueTicks]

noncomputable def literalKeyGraphStream_computableInPolyTime :
    TM2ComputableInPolyTime id id literalKeyGraphStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    emptyHeader_computableInPolyTime allTaggedKeyStream_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [← literalKeyGraphStream_eq] at output
        exact output }

def queryPairLeft (input : List CNFSym) : List (Option CliqueSym) :=
  OptionPairLeft.format
    ((rawCandidatePairs input).flatMap encodeCliqueEdge)

def graphPairRight (input : List CNFSym) : List (Option CliqueSym) :=
  (literalKeyGraphStream input).map some

def rawCandidatePairStream (input : List CNFSym) : List CliqueSym :=
  (rawCandidatePairs input).flatMap encodeCliqueEdge

noncomputable def rawCandidatePairStream_computableInPolyTime :
    TM2ComputableInPolyTime id id rawCandidatePairStream := by
  let raw := rawCandidatePairs_computableInPolyTime
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        simpa [rawCandidatePairStream] using raw.outputsFun input }

noncomputable def queryPairLeft_computableInPolyTime :
    TM2ComputableInPolyTime id id queryPairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawCandidatePairStream_computableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  exact Classical.choice composed

noncomputable def graphPairRight_computableInPolyTime :
    TM2ComputableInPolyTime id id graphPairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    literalKeyGraphStream_computableInPolyTime
    (someMap_computableInPolyTime CliqueSym)
  exact Classical.choice composed

def batchInput (input : List CNFSym) :
    List (Nat × Nat) × CliqueInstance :=
  (rawCandidatePairs input, literalKeyInstance input)

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
          OptionPairLeft.format, literalKeyGraphStream,
          List.append_assoc] using output }

def lookupResults (input : List CNFSym) : List Bool :=
  BatchEdgeLookup.batchResultStream
    (literalKeyInstance input) (rawCandidatePairs input)

noncomputable def lookupResults_computableInPolyTime :
    TM2ComputableInPolyTime id id lookupResults := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchInput_computableInPolyTime BatchEdgeLookup.batchResultsComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => BatchEdgeLookup.batchResultStream
      (literalKeyInstance input) (rawCandidatePairs input))
  simpa only [Function.comp_def, batchInput] using Classical.choice composed

def literalMembershipBits (input : List CNFSym) : List Bool :=
  (rawCandidatePairs input).map fun edge =>
    decide (edge ∈ (literalKeyInstance input).edges)

theorem dropHead_lookupResults (input : List CNFSym) :
    DropHead.stream (lookupResults input) = literalMembershipBits input := by
  simp [lookupResults, BatchEdgeLookup.batchResultStream,
    BatchEdgeLookup.queryMembershipBits, literalMembershipBits,
    DropHead.stream]

noncomputable def literalMembershipBits_computableInPolyTime :
    TM2ComputableInPolyTime id id literalMembershipBits := by
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

end PricingWithTips.FixedShapeLiteralMembershipTM2


