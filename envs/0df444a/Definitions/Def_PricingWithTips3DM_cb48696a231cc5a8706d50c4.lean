-- Prove2me | Definitions.Def_PricingWithTips3DM_cb48696a231cc5a8706d50c4
-- name    : PricingWithTips3DM_cb48696a231cc5a8706d50c4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:59:43.043806+00:00
-- url     : https://prove2.me/theorems/97e21eca-3464-4407-8247-3158f5af9e65
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapePaddingSelectorTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_df037b47dab89115cb9b431f
import Definitions.Def_PricingWithTips3DM_847398c5665bf6e2d87e2584
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Select exactly the two tautological padding literals which are present in
each clause.  This reuses the verified VERTEX-COVER record selector: because
that selector drops a record on `true`, we negate the membership stream first.
-/

noncomputable section

namespace PricingWithTips.FixedShapePaddingSelectorTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
open _root_.Turing
open PricingWithTips.FixedShapeClauseMembershipTM2
open PricingWithTips.FixedShapePaddingKeysTM2

def someMapSpec : StatefulFlatMapSpec Unit CliqueSym (Option CliqueSym) where
  initial := ()
  action _ symbol := ([some symbol], ())
  finish _ := []

private theorem someMapSpec_eq (input : List CliqueSym) :
    rewriteStatefulFlatMap someMapSpec input = input.map some := by
  unfold rewriteStatefulFlatMap
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      exact congrArg (some symbol :: ·) ih

noncomputable def someMap_computableInPolyTime :
    TM2ComputableInPolyTime id id (List.map (@some CliqueSym)) := by
  let machine := statefulFlatMap_computableInPolyTime someMapSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        simpa [someMapSpec_eq] using machine.outputsFun input }

def allPaddingCandidates (input : List CNFSym) : List (Nat × Nat) :=
  (List.range input.length).map (fun q => (q, 0)) ++
    (List.range input.length).map (fun q => (q, 1))

theorem allPaddingCandidateStream_eq (input : List CNFSym) :
    allPaddingCandidateStream input =
      (allPaddingCandidates input).flatMap encodeCliqueEdge := by
  rw [allPaddingCandidateStream, allPositivePaddingCandidateStream_eq]
  simp [allPaddingCandidates, List.flatMap_map,
    PricingWithTips.FixedShapeBaseClauseIndicesTM2.allClauseEdgeStream]

def retainPaddingBits (input : List CNFSym) : List Bool :=
  (duplicatedPaddingBits input).map Bool.not

theorem retainPaddingBits_length (input : List CNFSym) :
    (allPaddingCandidates input).length = (retainPaddingBits input).length := by
  simp [allPaddingCandidates, retainPaddingBits, duplicatedPaddingBits,
    paddingClauseMembershipBits_eq]

def alignedInput (input : List CNFSym) : Selector.AlignedInput :=
  ⟨(allPaddingCandidates input, retainPaddingBits input),
    retainPaddingBits_length input⟩

def candidatePairLeft (input : List CNFSym) : List (Option CliqueSym) :=
  OptionPairLeft.format (allPaddingCandidateStream input).reverse

noncomputable def candidatePairLeft_computableInPolyTime :
    TM2ComputableInPolyTime id id candidatePairLeft := by
  let reversed := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    allPaddingCandidateStream_computableInPolyTime
    (reverse_computableInPolyTime (Γ := CliqueSym)))
  exact Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    reversed (OptionPairLeft.computableInPolyTime CliqueSym))

def selectorBitsRight (input : List CNFSym) : List (Option CliqueSym) :=
  ((retainPaddingBits input).map Selector.selectorBitSymbol).map some

noncomputable def selectorBitsRight_computableInPolyTime :
    TM2ComputableInPolyTime id id selectorBitsRight := by
  let negated := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    duplicatedPaddingBits_computableInPolyTime
    (listMap_computableInPolyTime Bool.not))
  let tagged := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    negated (listMap_computableInPolyTime Selector.selectorBitSymbol))
  let optioned := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    tagged someMap_computableInPolyTime)
  change TM2ComputableInPolyTime id id
    (fun input => (((duplicatedPaddingBits input).map Bool.not).map
      Selector.selectorBitSymbol).map some)
  simpa only [List.map_map, Function.comp_def] using optioned

def encodeOptionCliqueSymPair :
    Option CliqueSym → UnaryFrameSym × UnaryFrameSym
  | some symbol => encodeCliqueSymPair symbol
  | none => (.frameEnd, .frameEnd)

def decodeOptionCliqueSymPair :
    UnaryFrameSym → UnaryFrameSym → Option CliqueSym
  | .frameEnd, .frameEnd => none
  | left, right => some (decodeCliqueSymPair left right)

@[simp] theorem decode_encodeOptionCliqueSymPair (symbol : Option CliqueSym) :
    decodeOptionCliqueSymPair (encodeOptionCliqueSymPair symbol).1
      (encodeOptionCliqueSymPair symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some symbol => cases symbol <;> rfl

theorem alignedInputEncoding_eq (input : List CNFSym) :
    Selector.alignedInputEncoding (alignedInput input) =
      candidatePairLeft input ++ selectorBitsRight input := by
  simp [Selector.alignedInputEncoding, Selector.inputEncoding, alignedInput,
    candidatePairLeft, selectorBitsRight, pairEncoding,
    allPaddingCandidateStream_eq, OptionPairLeft.format, List.map_reverse]

noncomputable def alignedInput_computableInPolyTime :
    TM2ComputableInPolyTime id Selector.alignedInputEncoding alignedInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeOptionCliqueSymPair decodeOptionCliqueSymPair
    decode_encodeOptionCliqueSymPair
    candidatePairLeft_computableInPolyTime
    selectorBitsRight_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [← alignedInputEncoding_eq input] at output
        exact output }

def selectedPaddingStream (input : List CNFSym) : List CliqueSym :=
  Selector.alignedSelectedStream (alignedInput input)

noncomputable def selectedPaddingStream_computableInPolyTime :
    TM2ComputableInPolyTime id id selectedPaddingStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    alignedInput_computableInPolyTime Selector.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => Selector.alignedSelectedStream (alignedInput input))
  simpa only [Function.comp_def] using Classical.choice composed

end PricingWithTips.FixedShapePaddingSelectorTM2


