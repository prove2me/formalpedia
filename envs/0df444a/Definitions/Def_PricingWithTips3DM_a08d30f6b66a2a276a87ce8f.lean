-- Prove2me | Definitions.Def_PricingWithTips3DM_a08d30f6b66a2a276a87ce8f
-- name    : PricingWithTips3DM_a08d30f6b66a2a276a87ce8f
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:35:51.737763+00:00
-- url     : https://prove2.me/theorems/e31f59f9-961e-4e76-99ac-e1bd3ada6858
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeLiteralSelectorTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_ddacc2a9bb82165e591a45f7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Select the structural raw pairs using the position-aligned literal
membership bits, then collapse each endpoint pair to the unary cell ordinal
stored as the second endpoint of `(0, ordinal)`. -/

noncomputable section

namespace PricingWithTips.FixedShapeLiteralSelectorTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
open _root_.Turing
open PricingWithTips.FixedShapeStructuralCandidatesTM2
open PricingWithTips.FixedShapeLiteralMembershipTM2
open PricingWithTips.FixedShapePairAlignment
open PricingWithTips.FixedShapeClauseMembershipTM2

def retainBits (input : List CNFSym) : List Bool :=
  (literalMembershipBits input).map Bool.not

theorem retainBits_length (input : List CNFSym) :
    (rawStructuralPairs input).length = (retainBits input).length := by
  simp only [retainBits, List.length_map]
  exact structural_membership_lengths input

def alignedInput (input : List CNFSym) : Selector.AlignedInput :=
  ⟨(rawStructuralPairs input, retainBits input), retainBits_length input⟩

def rawStructuralPairStream (input : List CNFSym) : List CliqueSym :=
  (rawStructuralPairs input).flatMap encodeCliqueEdge

noncomputable def rawStructuralPairStream_computableInPolyTime :
    TM2ComputableInPolyTime id id rawStructuralPairStream := by
  let raw := rawStructuralPairs_computableInPolyTime
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        simpa [rawStructuralPairStream] using raw.outputsFun input }

def candidatePairLeft (input : List CNFSym) : List (Option CliqueSym) :=
  OptionPairLeft.format (rawStructuralPairStream input).reverse

noncomputable def candidatePairLeft_computableInPolyTime :
    TM2ComputableInPolyTime id id candidatePairLeft := by
  let reversed := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawStructuralPairStream_computableInPolyTime
    (reverse_computableInPolyTime (Γ := CliqueSym)))
  exact Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    reversed (OptionPairLeft.computableInPolyTime CliqueSym))

def selectorBitsRight (input : List CNFSym) : List (Option CliqueSym) :=
  ((retainBits input).map Selector.selectorBitSymbol).map some

noncomputable def selectorBitsRight_computableInPolyTime :
    TM2ComputableInPolyTime id id selectorBitsRight := by
  let negated := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    literalMembershipBits_computableInPolyTime
    (listMap_computableInPolyTime Bool.not))
  let tagged := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    negated (listMap_computableInPolyTime Selector.selectorBitSymbol))
  let optioned := Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    tagged (someMap_computableInPolyTime CliqueSym))
  change TM2ComputableInPolyTime id id
    (fun input => (((literalMembershipBits input).map Bool.not).map
      Selector.selectorBitSymbol).map some)
  simpa only [List.map_map, Function.comp_def] using optioned

theorem alignedInputEncoding_eq (input : List CNFSym) :
    Selector.alignedInputEncoding (alignedInput input) =
      candidatePairLeft input ++ selectorBitsRight input := by
  simp [Selector.alignedInputEncoding, Selector.inputEncoding, alignedInput,
    candidatePairLeft, selectorBitsRight, pairEncoding,
    rawStructuralPairStream, OptionPairLeft.format, List.map_reverse]

noncomputable def alignedInput_computableInPolyTime :
    TM2ComputableInPolyTime id Selector.alignedInputEncoding alignedInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    PricingWithTips.FixedShapeClauseMembershipTM2.encodeOptionCliqueSymPair
    PricingWithTips.FixedShapeClauseMembershipTM2.decodeOptionCliqueSymPair
    PricingWithTips.FixedShapeClauseMembershipTM2.decode_encodeOptionCliqueSymPair
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

def selectedStructuralPairs (input : List CNFSym) : List (Nat × Nat) :=
  Selector.alignedSelectedEdges (alignedInput input)

def selectedStructuralStream (input : List CNFSym) : List CliqueSym :=
  Selector.alignedSelectedStream (alignedInput input)

theorem selectedStructuralStream_eq (input : List CNFSym) :
    selectedStructuralStream input =
      (selectedStructuralPairs input).flatMap encodeCliqueEdge := by
  rfl

noncomputable def selectedStructuralStream_computableInPolyTime :
    TM2ComputableInPolyTime id id selectedStructuralStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    alignedInput_computableInPolyTime Selector.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => Selector.alignedSelectedStream (alignedInput input))
  simpa only [Function.comp_def] using Classical.choice composed

def sumPairSpec : StatefulFlatMapSpec Unit CliqueSym CliqueSym where
  initial := ()
  action _ symbol :=
    match symbol with
    | .edgeMark => ([.edgeMark, .pairSep], ())
    | .tick => ([.tick], ())
    | .pairSep => ([], ())
    | .recordEnd => ([.recordEnd], ())
    | _ => ([], ())
  finish _ := []

def sumPairStream (input : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap sumPairSpec input

noncomputable def sumPairStream_computableInPolyTime :
    TM2ComputableInPolyTime id id sumPairStream :=
  statefulFlatMap_computableInPolyTime sumPairSpec

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem sum_ticks (count : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom sumPairSpec ()
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteStatefulFlatMapFrom sumPairSpec () tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      change .tick :: rewriteStatefulFlatMapFrom sumPairSpec ()
          (List.replicate count .tick ++ tail) = _
      rw [ih]
      simp only [List.cons_append]

private theorem sum_one (left right : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom sumPairSpec ()
        (encodeCliqueEdge (left, right) ++ tail) =
      encodeCliqueEdge (0, left + right) ++
        rewriteStatefulFlatMapFrom sumPairSpec () tail := by
  simp only [encodeCliqueEdge, prependCliqueTicks_eq_replicate,
    List.cons_append, List.append_assoc]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  change .edgeMark :: .pairSep ::
      rewriteStatefulFlatMapFrom sumPairSpec ()
        (List.replicate left .tick ++ .pairSep ::
          (List.replicate right .tick ++ .recordEnd :: tail)) = _
  rw [sum_ticks, rewriteStatefulFlatMapFrom.eq_def]
  change .edgeMark :: .pairSep ::
      (List.replicate left .tick ++
        rewriteStatefulFlatMapFrom sumPairSpec ()
          (List.replicate right .tick ++ .recordEnd :: tail)) = _
  rw [sum_ticks, rewriteStatefulFlatMapFrom.eq_def]
  change .edgeMark :: .pairSep ::
      (List.replicate left .tick ++
        (List.replicate right .tick ++ .recordEnd ::
          rewriteStatefulFlatMapFrom sumPairSpec () tail)) = _
  rw [← List.append_assoc, ← List.replicate_add]
  rfl

theorem sum_pairs (pairs : List (Nat × Nat)) :
    sumPairStream (pairs.flatMap encodeCliqueEdge) =
      (pairs.map fun pair => (0, pair.1 + pair.2)).flatMap
        encodeCliqueEdge := by
  unfold sumPairStream rewriteStatefulFlatMap
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨left, right⟩
      rw [List.flatMap_cons, sum_one]
      simp only [List.map_cons, List.flatMap_cons]
      rw [ih]

def literalEdgeStream (input : List CNFSym) : List CliqueSym :=
  sumPairStream (selectedStructuralStream input)

def literalEdges (input : List CNFSym) : List (Nat × Nat) :=
  (selectedStructuralPairs input).map fun pair => (0, pair.1 + pair.2)

theorem literalEdgeStream_eq (input : List CNFSym) :
    literalEdgeStream input =
      (literalEdges input).flatMap encodeCliqueEdge := by
  rw [literalEdgeStream, selectedStructuralStream_eq, sum_pairs]
  rfl

noncomputable def literalEdgeStream_computableInPolyTime :
    TM2ComputableInPolyTime id id literalEdgeStream :=
  Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    selectedStructuralStream_computableInPolyTime
    sumPairStream_computableInPolyTime)

end PricingWithTips.FixedShapeLiteralSelectorTM2


