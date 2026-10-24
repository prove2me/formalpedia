-- Prove2me | Definitions.Def_PricingWithTips3DM_df037b47dab89115cb9b431f
-- name    : PricingWithTips3DM_df037b47dab89115cb9b431f
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:55:32.028983+00:00
-- url     : https://prove2.me/theorems/58657801-fd21-45e2-a3d0-0231b55b1013
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapePaddingKeysTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_a0b3f1a7d600b0df4bcc86f8
import Definitions.Def_PricingWithTips3DM_4df0781f09048295ca076ad8
import Definitions.Def_PricingWithTips3DM_8169be64da1591889851249c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Native candidate streams and selectors for the two tautological literals
inserted in every padding clause. -/

noncomputable section

namespace PricingWithTips.FixedShapePaddingKeysTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open _root_.Turing
open PricingWithTips.FixedShapeBaseClauseIndicesTM2
open PricingWithTips.FixedShapeClauseMembershipTM2

def addOneToSecondSpec : StatefulFlatMapSpec Unit CliqueSym CliqueSym where
  initial := ()
  action _ symbol :=
    match symbol with
    | .recordEnd => ([.tick, .recordEnd], ())
    | _ => ([symbol], ())
  finish _ := []

def addOneToSecond (input : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap addOneToSecondSpec input

noncomputable def addOneToSecond_computableInPolyTime :
    TM2ComputableInPolyTime id id addOneToSecond :=
  statefulFlatMap_computableInPolyTime addOneToSecondSpec

private theorem addOne_prepend_ticks (q : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom addOneToSecondSpec ()
        (prependCliqueTicks q tail) =
      prependCliqueTicks q
        (rewriteStatefulFlatMapFrom addOneToSecondSpec () tail) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [prependCliqueTicks, rewriteStatefulFlatMapFrom.eq_def]
      change .tick :: rewriteStatefulFlatMapFrom addOneToSecondSpec ()
          (prependCliqueTicks q tail) =
        .tick :: prependCliqueTicks q
          (rewriteStatefulFlatMapFrom addOneToSecondSpec () tail)
      rw [ih]

private theorem addOne_edge (q : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom addOneToSecondSpec ()
        (encodeCliqueEdge (q, 0) ++ tail) =
      encodeCliqueEdge (q, 1) ++
        rewriteStatefulFlatMapFrom addOneToSecondSpec () tail := by
  simp only [encodeCliqueEdge, List.cons_append, List.nil_append,
    prependCliqueTicks_append]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  change .edgeMark :: rewriteStatefulFlatMapFrom addOneToSecondSpec ()
      (prependCliqueTicks q (.pairSep :: .recordEnd :: tail)) = _
  rw [addOne_prepend_ticks]
  have htail : rewriteStatefulFlatMapFrom addOneToSecondSpec ()
      (.pairSep :: .recordEnd :: tail) =
      .pairSep :: .tick :: .recordEnd ::
        rewriteStatefulFlatMapFrom addOneToSecondSpec () tail := by
    rw [rewriteStatefulFlatMapFrom.eq_def]
    change .pairSep :: rewriteStatefulFlatMapFrom addOneToSecondSpec ()
        (.recordEnd :: tail) = _
    rw [rewriteStatefulFlatMapFrom.eq_def]
    rfl
  rw [htail]
  rfl

def allPositivePaddingCandidateStream (input : List CNFSym) : List CliqueSym :=
  addOneToSecond (allClauseEdgeStream input)

theorem allPositivePaddingCandidateStream_eq (input : List CNFSym) :
    allPositivePaddingCandidateStream input =
      (List.range input.length).flatMap
        (fun index => encodeCliqueEdge (index, 1)) := by
  unfold allPositivePaddingCandidateStream addOneToSecond
    allClauseEdgeStream
  change rewriteStatefulFlatMapFrom addOneToSecondSpec ()
      ((List.range input.length).flatMap
        (fun index => encodeCliqueEdge (index, 0))) = _
  induction (List.range input.length) with
  | nil => rfl
  | cons q qs ih =>
      rw [List.flatMap_cons, addOne_edge, ih, List.flatMap_cons]

noncomputable def allPositivePaddingCandidateStream_computableInPolyTime :
    TM2ComputableInPolyTime id id allPositivePaddingCandidateStream := by
  exact Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    allClauseEdgeStream_computableInPolyTime
    addOneToSecond_computableInPolyTime)

def allPaddingCandidateStream (input : List CNFSym) : List CliqueSym :=
  allClauseEdgeStream input ++ allPositivePaddingCandidateStream input

noncomputable def allPaddingCandidateStream_computableInPolyTime :
    TM2ComputableInPolyTime id id allPaddingCandidateStream := by
  exact fixedPairSameInputConcat_computableInPolyTime
    PricingWithTips.FixedShapeGuardedKeysTM2.encodePair
    PricingWithTips.FixedShapeGuardedKeysTM2.decodePair
    PricingWithTips.FixedShapeGuardedKeysTM2.decode_encodePair
    allClauseEdgeStream_computableInPolyTime
    allPositivePaddingCandidateStream_computableInPolyTime

def encodeBoolPair : Bool → UnaryFrameSym × UnaryFrameSym
  | true => (.tick, .tick)
  | false => (.tick, .separator)

def decodeBoolPair : UnaryFrameSym → UnaryFrameSym → Bool
  | .tick, .tick => true
  | _, _ => false

@[simp] theorem decode_encodeBoolPair (b : Bool) :
    decodeBoolPair (encodeBoolPair b).1 (encodeBoolPair b).2 = b := by
  cases b <;> rfl

def duplicatedPaddingBits (input : List CNFSym) : List Bool :=
  paddingClauseMembershipBits input ++ paddingClauseMembershipBits input

noncomputable def duplicatedPaddingBits_computableInPolyTime :
    TM2ComputableInPolyTime id id duplicatedPaddingBits := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeBoolPair decodeBoolPair decode_encodeBoolPair
    paddingClauseMembershipBits_computableInPolyTime
    paddingClauseMembershipBits_computableInPolyTime

end PricingWithTips.FixedShapePaddingKeysTM2


