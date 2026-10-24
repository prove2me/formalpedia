-- Prove2me | Definitions.Def_PricingWithTips3DM_4deaeff7419f12b9a2736f4b
-- name    : PricingWithTips3DM_4deaeff7419f12b9a2736f4b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:44:53.767788+00:00
-- url     : https://prove2.me/theorems/f472d4e1-b2ab-4f4e-82ce-dcfde6d451f3
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeBaseClauseIndicesTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_f6bf858856e0a0132109161e
import Definitions.Def_PricingWithTips3DM_9df43c61d525d4d6abb73fc3
import Definitions.Def_PricingWithTips3DM_7937e4ad7b8976e2b47d692e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Native enumeration of the clause indices belonging to `baseCNF`.

The existing CLRS header machine already computes the decoded clause count.
We prefix its output by the existing 3-CNF-validity flag, then use one fixed
transducer to select the clause-count field.  On malformed input it emits one
unit, matching the sentinel formula `[[]]`.  Feeding that clock to the
verified unary-index machine enumerates precisely `0, ..., baseCNF.length-1`.
-/

noncomputable section

namespace PricingWithTips.FixedShapeBaseClauseIndicesTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeGuardedKeysTM2
open _root_.Turing

def flaggedHeaderInput (input : List CNFSym) : List CliqueSym :=
  canonicalFlagStream input ++ canonicalCliqueHeader input

noncomputable def flaggedHeaderInput_computableInPolyTime :
    TM2ComputableInPolyTime id id flaggedHeaderInput := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    canonicalFlagStream_computableInPolyTime
    canonicalCliqueHeader_computableInPolyTime

abbrev CountMode := Bool × Bool × Bool

private def startMode : CountMode := (false, false, false)
private def verticesMode : CountMode := (true, false, false)
private def clausesMode : CountMode := (false, true, false)
private def invalidMode : CountMode := (true, true, false)
private def doneMode : CountMode := (false, false, true)

def countSpec : StatefulFlatMapSpec CountMode CliqueSym Unit where
  initial := startMode
  action mode symbol :=
    if mode = startMode then
      if symbol = .instanceMark then ([], verticesMode) else ([], invalidMode)
    else if mode = verticesMode then
      if symbol = .fieldSep then ([], clausesMode) else ([], verticesMode)
    else if mode = clausesMode then
      if symbol = .tick then ([()], clausesMode) else ([], doneMode)
    else if mode = invalidMode then ([], invalidMode)
    else ([], doneMode)
  finish mode := if mode = invalidMode then [()] else []

def baseClauseClock (input : List CliqueSym) : List Unit :=
  rewriteStatefulFlatMap countSpec input

noncomputable def baseClauseClock_computableInPolyTime :
    TM2ComputableInPolyTime id id baseClauseClock :=
  statefulFlatMap_computableInPolyTime countSpec

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem vertices_ticks (count : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom countSpec verticesMode
        (List.replicate count .tick ++ .fieldSep :: tail) =
      rewriteStatefulFlatMapFrom countSpec clausesMode tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      exact ih

private theorem clauses_ticks (count : Nat) :
    rewriteStatefulFlatMapFrom countSpec clausesMode
        (List.replicate count .tick ++ [.fieldSep]) =
      List.replicate count () := by
  induction count with
  | zero =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      change () :: rewriteStatefulFlatMapFrom countSpec clausesMode
          (List.replicate count .tick ++ [.fieldSep]) = _
      rw [ih]
      simpa [List.replicate_succ]

private theorem invalid_run (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom countSpec invalidMode input = [()] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      exact ih

theorem baseClauseClock_flag_header (valid : Bool)
    (vertices clauses : Nat) :
    baseClauseClock
        (flagSymbol valid :: .instanceMark ::
          prependCliqueTicks vertices
            (.fieldSep :: prependCliqueTicks clauses [.fieldSep])) =
      List.replicate (if valid then clauses else 1) () := by
  cases valid with
  | false =>
      change rewriteStatefulFlatMapFrom countSpec invalidMode
          (.instanceMark :: prependCliqueTicks vertices
            (.fieldSep :: prependCliqueTicks clauses [.fieldSep])) = [()]
      exact invalid_run _
  | true =>
      change rewriteStatefulFlatMapFrom countSpec verticesMode
          (.instanceMark :: prependCliqueTicks vertices
            (.fieldSep :: prependCliqueTicks clauses [.fieldSep])) =
        List.replicate clauses ()
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change rewriteStatefulFlatMapFrom countSpec verticesMode
          (prependCliqueTicks vertices
            (.fieldSep :: prependCliqueTicks clauses [.fieldSep])) = _
      simp only [prependCliqueTicks_eq_replicate]
      rw [vertices_ticks]
      exact clauses_ticks clauses

theorem baseClauseClock_flaggedHeaderInput (input : List CNFSym) :
    baseClauseClock (flaggedHeaderInput input) =
      List.replicate (baseCNF input).length () := by
  rw [flaggedHeaderInput, canonicalFlagStream, canonicalThreeCNFFlag_eq,
    canonicalCliqueHeader_eq]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  rw [baseClauseClock_flag_header]
  by_cases h : isThreeCNFBool (decodeCNF input) = true
  · have hp : IsThreeCNF (decodeCNF input) :=
      (isThreeCNFBool_eq_true _).1 h
    simp [h, hp, baseCNF, PricingWithTips.CLRS3CNFBridge.guardedCertCNF,
      Hardness.Cert.length_decodeCNF, PricingWithTips.CLRS3CNFBridge.certCNF]
  · have hf : isThreeCNFBool (decodeCNF input) = false := by
      cases he : isThreeCNFBool (decodeCNF input)
      · rfl
      · exact False.elim (h he)
    have hp : ¬ IsThreeCNF (decodeCNF input) := by
      intro hp
      exact h ((isThreeCNFBool_eq_true _).2 hp)
    simp [hf, hp, baseCNF, PricingWithTips.CLRS3CNFBridge.guardedCertCNF,
      Hardness.Cert.length_decodeCNF]

def canonicalBaseClauseClock (input : List CNFSym) : List Unit :=
  baseClauseClock (flaggedHeaderInput input)

noncomputable def canonicalBaseClauseClock_computableInPolyTime :
    TM2ComputableInPolyTime id id canonicalBaseClauseClock := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    flaggedHeaderInput_computableInPolyTime baseClauseClock_computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => baseClauseClock (flaggedHeaderInput input))
  simpa [Function.comp_def] using Classical.choice composed

def baseClauseIndexStream (input : List CNFSym) : List Bool :=
  unaryIndexStream (baseCNF input).length

theorem unaryIndex_canonicalBaseClauseClock (input : List CNFSym) :
    unaryIndexStream (canonicalBaseClauseClock input).length =
      baseClauseIndexStream input := by
  rw [canonicalBaseClauseClock, baseClauseClock_flaggedHeaderInput]
  simp [baseClauseIndexStream]

/-- Native enumeration of exactly the clause indices occupied by `baseCNF`. -/
noncomputable def baseClauseIndexStream_computableInPolyTime :
    TM2ComputableInPolyTime id id baseClauseIndexStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    canonicalBaseClauseClock_computableInPolyTime
    unaryIndexStream_computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simp only [Function.comp_apply, id_eq] at output
        rw [unaryIndex_canonicalBaseClauseClock] at output
        exact output }

def clauseIndexEdgeFormatterSpec : StatefulFlatMapSpec Bool Bool CliqueSym where
  initial := true
  action atStart symbol :=
    if symbol then
      (if atStart then [.edgeMark, .tick] else [.tick], false)
    else
      (if atStart then [.edgeMark, .pairSep, .recordEnd]
        else [.pairSep, .recordEnd], true)
  finish _ := []

def clauseIndexEdgeFormatter (input : List Bool) : List CliqueSym :=
  rewriteStatefulFlatMap clauseIndexEdgeFormatterSpec input

noncomputable def clauseIndexEdgeFormatter_computableInPolyTime :
    TM2ComputableInPolyTime id id clauseIndexEdgeFormatter :=
  statefulFlatMap_computableInPolyTime clauseIndexEdgeFormatterSpec

private theorem formatter_index_append (index : Nat) (tail : List Bool) :
    rewriteStatefulFlatMapFrom clauseIndexEdgeFormatterSpec true
        (unaryIndexCode index ++ tail) =
      encodeCliqueEdge (index, 0) ++
        rewriteStatefulFlatMapFrom clauseIndexEdgeFormatterSpec true tail := by
  cases index with
  | zero => rfl
  | succ index =>
      rw [show unaryIndexCode (index + 1) ++ tail =
          true :: (List.replicate index true ++ false :: tail) by
        simp [unaryIndexCode, List.replicate_succ, List.append_assoc]]
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change .edgeMark :: .tick ::
          rewriteStatefulFlatMapFrom clauseIndexEdgeFormatterSpec false
            (List.replicate index true ++ false :: tail) = _
      have inside : rewriteStatefulFlatMapFrom clauseIndexEdgeFormatterSpec false
          (List.replicate index true ++ false :: tail) =
          List.replicate index .tick ++ [.pairSep, .recordEnd] ++
            rewriteStatefulFlatMapFrom clauseIndexEdgeFormatterSpec true tail := by
        induction index with
        | zero => rfl
        | succ index ih =>
            rw [List.replicate_succ, List.cons_append,
              rewriteStatefulFlatMapFrom.eq_def]
            change .tick ::
                rewriteStatefulFlatMapFrom clauseIndexEdgeFormatterSpec false
                  (List.replicate index true ++ false :: tail) = _
            rw [ih]
            simp [List.replicate_succ]
      rw [inside]
      simp [encodeCliqueEdge, prependCliqueTicks_eq_replicate,
        List.replicate_succ, List.append_assoc]

private theorem formatter_indices_from (indices : List Nat) :
    rewriteStatefulFlatMapFrom clauseIndexEdgeFormatterSpec true
        (indices.flatMap unaryIndexCode) =
      indices.flatMap (fun index => encodeCliqueEdge (index, 0)) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      rw [List.flatMap_cons, List.flatMap_cons]
      rw [formatter_index_append, ih]

theorem clauseIndexEdgeFormatter_unaryIndexStream (count : Nat) :
    clauseIndexEdgeFormatter (unaryIndexStream count) =
      (List.range count).flatMap (fun index => encodeCliqueEdge (index, 0)) := by
  exact formatter_indices_from (List.range count)

def baseClauseEdgeStream (input : List CNFSym) : List CliqueSym :=
  (List.range (baseCNF input).length).flatMap
    (fun index => encodeCliqueEdge (index, 0))

/-- Native sparse edge table whose first coordinates are precisely the clause
indices occupied by the guarded base formula. -/
noncomputable def baseClauseEdgeStream_computableInPolyTime :
    TM2ComputableInPolyTime id id baseClauseEdgeStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    baseClauseIndexStream_computableInPolyTime
    clauseIndexEdgeFormatter_computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simp only [Function.comp_apply, id_eq] at output
        change TM2OutputsInTime machine.tm
          (List.map machine.inputAlphabet.invFun input)
          (some (List.map machine.outputAlphabet.invFun
            (clauseIndexEdgeFormatter
              (unaryIndexStream (baseCNF input).length))))
          (Polynomial.eval input.length machine.time) at output
        rw [clauseIndexEdgeFormatter_unaryIndexStream] at output
        exact output }

def allClauseEdgeStream (input : List CNFSym) : List CliqueSym :=
  (List.range input.length).flatMap
    (fun index => encodeCliqueEdge (index, 0))

noncomputable def inputUnitClock_computableInPolyTime :
    TM2ComputableInPolyTime id id (fun input : List CNFSym => input.map fun _ => ()) :=
  listMap_computableInPolyTime (fun _ : CNFSym => ())

/-- Native query stream `(0,0), ..., (L-1,0)` for deciding which of the `L`
fixed-shape clause positions belong to the guarded base formula. -/
noncomputable def allClauseEdgeStream_computableInPolyTime :
    TM2ComputableInPolyTime id id allClauseEdgeStream := by
  let indicesExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    inputUnitClock_computableInPolyTime unaryIndexStream_computableInPolyTime
  let indices := Classical.choice indicesExists
  let edgesExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    indices clauseIndexEdgeFormatter_computableInPolyTime
  let machine := Classical.choice edgesExists
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simp only [Function.comp_apply, id_eq, List.length_map] at output
        rw [clauseIndexEdgeFormatter_unaryIndexStream] at output
        exact output }

end PricingWithTips.FixedShapeBaseClauseIndicesTM2


