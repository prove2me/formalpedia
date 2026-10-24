-- Prove2me | Definitions.Def_PricingWithTips3DM_4df0781f09048295ca076ad8
-- name    : PricingWithTips3DM_4df0781f09048295ca076ad8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:51:48.325151+00:00
-- url     : https://prove2.me/theorems/e4bf45d5-2204-4493-adee-d6b06d8edff0
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeClauseMembershipTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_4deaeff7419f12b9a2736f4b
import Definitions.Def_PricingWithTips3DM_96c0ded9337a34f5190dd45d
import Definitions.Def_PricingWithTips3DM_196af6a38e439e0e15d18b37
import Definitions.Def_PricingWithTips3DM_b6bd7fccce8d7d3f1596c77e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Batch recognition of the fixed-shape base/padding clause boundary. -/

noncomputable section

namespace PricingWithTips.FixedShapeClauseMembershipTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeBaseClauseIndicesTM2
open _root_.Turing

def someMapSpec (Γ : Type) : StatefulFlatMapSpec Unit Γ (Option Γ) where
  initial := ()
  action _ symbol := ([some symbol], ())
  finish _ := []

private theorem rewrite_someMapSpec_from {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMapFrom (someMapSpec Γ) () input = input.map some := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      change some symbol ::
          rewriteStatefulFlatMapFrom (someMapSpec Γ) () input =
        some symbol :: input.map some
      exact congrArg (some symbol :: ·) ih

@[simp] theorem rewrite_someMapSpec {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMap (someMapSpec Γ) input = input.map some :=
  rewrite_someMapSpec_from input

noncomputable def someMap_computableInPolyTime (Γ : Type) [Fintype Γ] :
    TM2ComputableInPolyTime id id (List.map (@some Γ)) := by
  let machine := statefulFlatMap_computableInPolyTime (someMapSpec Γ)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        simpa using machine.outputsFun input }

def encodeOptionCliqueSymPair :
    Option CliqueSym → UnaryFrameSym × UnaryFrameSym
  | some symbol => encodeCliqueSymPair symbol
  | none => (.frameEnd, .frameEnd)

def decodeOptionCliqueSymPair :
    UnaryFrameSym → UnaryFrameSym → Option CliqueSym
  | .frameEnd, .frameEnd => none
  | left, right => some (decodeCliqueSymPair left right)

@[simp] theorem decode_encodeOptionCliqueSymPair
    (symbol : Option CliqueSym) :
    decodeOptionCliqueSymPair (encodeOptionCliqueSymPair symbol).1
      (encodeOptionCliqueSymPair symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some symbol => cases symbol <;> rfl

def baseClauseInstance (input : List CNFSym) : CliqueInstance where
  vertexCount := 0
  targetSize := 0
  edges := (List.range (baseCNF input).length).map (fun q => (q, 0))

def clauseQueries (input : List CNFSym) : List (Nat × Nat) :=
  (List.range input.length).map (fun q => (q, 0))

@[simp] theorem clauseQueries_flatMap (input : List CNFSym) :
    (clauseQueries input).flatMap encodeCliqueEdge = allClauseEdgeStream input := by
  simp [clauseQueries, allClauseEdgeStream, List.flatMap_map,
    Function.comp_def]

@[simp] theorem baseClauseInstance_edges_flatMap (input : List CNFSym) :
    (baseClauseInstance input).edges.flatMap encodeCliqueEdge =
      baseClauseEdgeStream input := by
  simp [baseClauseInstance, baseClauseEdgeStream, List.flatMap_map,
    Function.comp_def]

def headerSpec : StatefulFlatMapSpec Unit CNFSym CliqueSym where
  initial := ()
  action _ _ := ([], ())
  finish _ := [.instanceMark, .fieldSep, .fieldSep]

def emptyHeader (input : List CNFSym) : List CliqueSym :=
  rewriteStatefulFlatMap headerSpec input

theorem emptyHeader_eq (input : List CNFSym) :
    emptyHeader input = [.instanceMark, .fieldSep, .fieldSep] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [emptyHeader, rewriteStatefulFlatMap]
      change rewriteStatefulFlatMapFrom headerSpec () (symbol :: input) = _
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change rewriteStatefulFlatMapFrom headerSpec () input = _
      simpa [emptyHeader, rewriteStatefulFlatMap] using ih

noncomputable def emptyHeader_computableInPolyTime :
    TM2ComputableInPolyTime id id emptyHeader :=
  statefulFlatMap_computableInPolyTime headerSpec

def baseGraphStream (input : List CNFSym) : List CliqueSym :=
  encodeCliqueInstance (baseClauseInstance input)

theorem baseGraphStream_eq (input : List CNFSym) :
    baseGraphStream input = emptyHeader input ++ baseClauseEdgeStream input := by
  rw [emptyHeader_eq]
  simp [baseGraphStream, encodeCliqueInstance, baseClauseInstance,
    baseClauseEdgeStream, List.flatMap_map, Function.comp_def,
    prependCliqueTicks]

noncomputable def baseGraphStream_computableInPolyTime :
    TM2ComputableInPolyTime id id baseGraphStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    emptyHeader_computableInPolyTime
    baseClauseEdgeStream_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [← baseGraphStream_eq] at output
        exact output }

def queryPairLeft (input : List CNFSym) : List (Option CliqueSym) :=
  OptionPairLeft.format (allClauseEdgeStream input)

def graphPairRight (input : List CNFSym) : List (Option CliqueSym) :=
  (baseGraphStream input).map some

noncomputable def queryPairLeft_computableInPolyTime :
    TM2ComputableInPolyTime id id queryPairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    allClauseEdgeStream_computableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  exact Classical.choice composed

noncomputable def graphPairRight_computableInPolyTime :
    TM2ComputableInPolyTime id id graphPairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    baseGraphStream_computableInPolyTime
    (someMap_computableInPolyTime CliqueSym)
  exact Classical.choice composed

def batchInput (input : List CNFSym) :
    List (Nat × Nat) × CliqueInstance :=
  (clauseQueries input, baseClauseInstance input)

noncomputable def batchInput_computableInPolyTime :
    TM2ComputableInPolyTime id
      (fun pr : List (Nat × Nat) × CliqueInstance =>
        pairEncoding (pr.1.flatMap encodeCliqueEdge)
          (encodeCliqueInstance pr.2)) batchInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeOptionCliqueSymPair decodeOptionCliqueSymPair
    decode_encodeOptionCliqueSymPair
    queryPairLeft_computableInPolyTime graphPairRight_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [batchInput, queryPairLeft, graphPairRight, pairEncoding,
          OptionPairLeft.format, baseGraphStream, clauseQueries_flatMap,
          List.append_assoc] using output }

def lookupResults (input : List CNFSym) : List Bool :=
  BatchEdgeLookup.batchResultStream
    (baseClauseInstance input) (clauseQueries input)

noncomputable def lookupResults_computableInPolyTime :
    TM2ComputableInPolyTime id id lookupResults := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    batchInput_computableInPolyTime BatchEdgeLookup.batchResultsComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => BatchEdgeLookup.batchResultStream
      (baseClauseInstance input) (clauseQueries input))
  simpa [Function.comp_def, batchInput] using Classical.choice composed

def baseClauseMembershipBits (input : List CNFSym) : List Bool :=
  (List.range input.length).map fun q => decide (q < (baseCNF input).length)

theorem queryMembershipBits_eq (input : List CNFSym) :
    BatchEdgeLookup.queryMembershipBits
        (baseClauseInstance input) (clauseQueries input) =
      baseClauseMembershipBits input := by
  simp [BatchEdgeLookup.queryMembershipBits, baseClauseInstance,
    clauseQueries, baseClauseMembershipBits]

theorem dropHead_lookupResults (input : List CNFSym) :
    DropHead.stream (lookupResults input) = baseClauseMembershipBits input := by
  simp [lookupResults, BatchEdgeLookup.batchResultStream,
    queryMembershipBits_eq, DropHead.stream]

/-- Native Boolean stream marking the base clauses among the `L` fixed-shape
positions; negating it marks exactly the padding clauses. -/
noncomputable def baseClauseMembershipBits_computableInPolyTime :
    TM2ComputableInPolyTime id id baseClauseMembershipBits := by
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

def paddingClauseMembershipBits (input : List CNFSym) : List Bool :=
  (baseClauseMembershipBits input).map (!·)

theorem paddingClauseMembershipBits_eq (input : List CNFSym) :
    paddingClauseMembershipBits input =
      (List.range input.length).map
        (fun q => decide ((baseCNF input).length ≤ q)) := by
  simp only [paddingClauseMembershipBits, baseClauseMembershipBits,
    List.map_map, Function.comp_apply]
  apply List.map_congr_left
  intro q hq
  by_cases h : q < (baseCNF input).length
  · have hn : ¬ (baseCNF input).length ≤ q := Nat.not_le_of_gt h
    simp [h, hn]
  · have hp : (baseCNF input).length ≤ q := Nat.le_of_not_gt h
    simp [h, hp]

noncomputable def paddingClauseMembershipBits_computableInPolyTime :
    TM2ComputableInPolyTime id id paddingClauseMembershipBits := by
  let negator := listMap_computableInPolyTime Bool.not
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    baseClauseMembershipBits_computableInPolyTime negator
  change TM2ComputableInPolyTime id id
    (fun input => (baseClauseMembershipBits input).map Bool.not)
  simpa [Function.comp_def] using Classical.choice composed

end PricingWithTips.FixedShapeClauseMembershipTM2


