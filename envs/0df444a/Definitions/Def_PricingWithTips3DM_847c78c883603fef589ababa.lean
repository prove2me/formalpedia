-- Prove2me | Definitions.Def_PricingWithTips3DM_847c78c883603fef589ababa
-- name    : PricingWithTips3DM_847c78c883603fef589ababa
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:58:04.612844+00:00
-- url     : https://prove2.me/theorems/bc6f1383-1037-41e4-982e-d4f5d55326b3
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeOccurrenceKeysTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_b062d0f04915c2cc3bdb50d7
import Definitions.Def_PricingWithTips3DM_adcbf99c0fa60800ad77bb94
import Definitions.Def_PricingWithTips3DM_d8886977e67d59ff4f35de9d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Literal-occurrence keys for the fixed-shape 3DM test family

The CLRS occurrence-row machine emits four unary fields
`[vertex, clause, polarityCode, variable + 1]`.  This fixed finite-state pass
discards the vertex and rewrites every remaining row to the canonical Clique
edge `(clause, 2 * variable + bit)`, where the bit convention is the one used
by the 3DM gadget (`positive = 1`, `negative = 0`).
-/

noncomputable section

namespace PricingWithTips.FixedShapeOccurrenceKeysTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open _root_.Turing

inductive Mode
  | vertex
  | clause
  | polarityStart
  | polarityNegative
  | variableFirst (positive : Bool)
  | variableRest (positive : Bool)
  | rowEnd
deriving DecidableEq, Fintype

/-- The occurrence-row to literal-key transducer.  The positive variable code
is decremented by dropping its first tick, then every remaining tick is
doubled. -/
def spec : StatefulFlatMapSpec Mode UnaryFrameSym CliqueSym where
  initial := .vertex
  action mode symbol :=
    match mode, symbol with
    | .vertex, .tick => ([], .vertex)
    | .vertex, .separator => ([.edgeMark], .clause)
    | .vertex, .frameEnd => ([], .vertex)
    | .clause, .tick => ([.tick], .clause)
    | .clause, .separator => ([.pairSep], .polarityStart)
    | .clause, .frameEnd => ([], .vertex)
    | .polarityStart, .tick => ([], .polarityNegative)
    | .polarityStart, .separator => ([], .variableFirst true)
    | .polarityStart, .frameEnd => ([], .vertex)
    | .polarityNegative, .tick => ([], .polarityNegative)
    | .polarityNegative, .separator => ([], .variableFirst false)
    | .polarityNegative, .frameEnd => ([], .vertex)
    | .variableFirst positive, .tick => ([], .variableRest positive)
    | .variableFirst positive, .separator =>
        (if positive then [.tick, .recordEnd] else [.recordEnd], .rowEnd)
    | .variableFirst _, .frameEnd => ([], .vertex)
    | .variableRest positive, .tick => ([.tick, .tick], .variableRest positive)
    | .variableRest positive, .separator =>
        (if positive then [.tick, .recordEnd] else [.recordEnd], .rowEnd)
    | .variableRest _, .frameEnd => ([], .vertex)
    | .rowEnd, .frameEnd => ([], .vertex)
    | .rowEnd, _ => ([], .rowEnd)
  finish _ := []

def occurrenceKeyStream (rows : List UnaryFrameSym) : List CliqueSym :=
  rewriteStatefulFlatMap spec rows

/-- The row-to-key pass is a fixed linear-time native Mathlib TM2. -/
noncomputable def occurrenceKeyStream_computableInPolyTime :
    TM2ComputableInPolyTime id id occurrenceKeyStream :=
  statefulFlatMap_computableInPolyTime spec

private theorem vertex_ticks (n : Nat) (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec .vertex
        (List.replicate n .tick ++ .separator :: tail) =
      .edgeMark :: rewriteStatefulFlatMapFrom spec .clause tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      exact ih

private theorem clause_ticks (n : Nat) (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec .clause
        (List.replicate n .tick ++ .separator :: tail) =
      prependCliqueTicks n
        (.pairSep :: rewriteStatefulFlatMapFrom spec .polarityStart tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def, prependCliqueTicks]
      exact congrArg (List.cons CliqueSym.tick) ih

private theorem variableRest_ticks (positive : Bool) (n : Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec (.variableRest positive)
        (List.replicate n .tick ++ .separator :: tail) =
      prependCliqueTicks (2 * n + positive.toNat)
        (.recordEnd :: rewriteStatefulFlatMapFrom spec .rowEnd tail) := by
  induction n with
  | zero => cases positive <;> rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      cases positive <;>
        simp only [Bool.toNat_false, Bool.toNat_true] at ih ⊢ <;>
        simp only [Nat.mul_succ, prependCliqueTicks] <;>
        exact congrArg (List.cons CliqueSym.tick)
          (congrArg (List.cons CliqueSym.tick) ih)

private theorem variable_ticks (positive : Bool) (n : Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec (.variableFirst positive)
        (List.replicate (n + 1) .tick ++ .separator :: tail) =
      prependCliqueTicks (2 * n + positive.toNat)
        (.recordEnd :: rewriteStatefulFlatMapFrom spec .rowEnd tail) := by
  rw [List.replicate_succ, List.cons_append,
    rewriteStatefulFlatMapFrom.eq_def]
  exact variableRest_ticks positive n tail

private theorem polarity (positive : Bool) (n : Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec .polarityStart
        (List.replicate (if positive then 0 else 1) .tick ++
          .separator ::
          (List.replicate (n + 1) .tick ++ .separator :: tail)) =
      prependCliqueTicks (2 * n + positive.toNat)
        (.recordEnd :: rewriteStatefulFlatMapFrom spec .rowEnd tail) := by
  cases positive with
  | false =>
      change rewriteStatefulFlatMapFrom spec (.variableFirst false)
          (List.replicate (n + 1) .tick ++ .separator :: tail) =
        prependCliqueTicks (2 * n + false.toNat)
          (.recordEnd :: rewriteStatefulFlatMapFrom spec .rowEnd tail)
      exact variable_ticks false n tail
  | true =>
      change rewriteStatefulFlatMapFrom spec (.variableFirst true)
          (List.replicate (n + 1) .tick ++ .separator :: tail) =
        prependCliqueTicks (2 * n + true.toNat)
          (.recordEnd :: rewriteStatefulFlatMapFrom spec .rowEnd tail)
      exact variable_ticks true n tail

/-- Exact action on one well-formed indexed occurrence row. -/
theorem one_row (vertex clause var : Nat) (positive : Bool)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec .vertex
        (encodeUnaryFrame [vertex, clause,
            if positive then 0 else 1, var + 1] ++
          .frameEnd :: tail) =
      encodeCliqueEdge (clause, 2 * var + positive.toNat) ++
        rewriteStatefulFlatMapFrom spec .vertex tail := by
  simp only [encodeUnaryFrame, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, encodeUnaryFrameBlock, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [vertex_ticks, clause_ticks, polarity]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  simp only [spec, List.nil_append, encodeCliqueEdge, List.cons_append,
    List.nil_append, prependCliqueTicks_append]

/-- Semantic key attached to one CLRS literal occurrence. -/
def literalKey (clause : Nat) : Literal → Nat × Nat
  | .pos var => (clause, 2 * var + 1)
  | .neg var => (clause, 2 * var)

def clauseKeys (clause : Nat) (literals : Clause) : List (Nat × Nat) :=
  literals.map (literalKey clause)

def formulaKeysFrom : Nat → CNF → List (Nat × Nat)
  | _, [] => []
  | clause, literals :: formula =>
      clauseKeys clause literals ++ formulaKeysFrom (clause + 1) formula

def formulaKeys (formula : CNF) : List (Nat × Nat) :=
  formulaKeysFrom 0 formula

private theorem clause_rows (vertex clause : Nat) (literals : Clause)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec .vertex
        (encodeIndexedClauseRowsFrom vertex clause literals ++ tail) =
      (clauseKeys clause literals).flatMap encodeCliqueEdge ++
        rewriteStatefulFlatMapFrom spec .vertex tail := by
  induction literals generalizing vertex with
  | nil => rfl
  | cons literal literals ih =>
      cases literal with
      | pos var =>
          simp only [encodeIndexedClauseRowsFrom, indexedOccurrenceRowValues,
            occurrencePolarityCode, occurrenceVariableCode, List.append_assoc,
            List.singleton_append]
          have hrow := one_row vertex clause var true
            (encodeIndexedClauseRowsFrom (vertex + 1) clause literals ++ tail)
          simp only [if_true] at hrow
          rw [List.cons_append]
          rw [hrow]
          simp only [clauseKeys, List.map_cons, List.flatMap_cons, literalKey,
            Bool.toNat_true, List.append_assoc]
          rw [ih (vertex := vertex + 1)]
          rfl
      | neg var =>
          simp only [encodeIndexedClauseRowsFrom, indexedOccurrenceRowValues,
            occurrencePolarityCode, occurrenceVariableCode, List.append_assoc,
            List.singleton_append]
          have hrow := one_row vertex clause var false
            (encodeIndexedClauseRowsFrom (vertex + 1) clause literals ++ tail)
          simp only [Bool.false_eq_true, if_false] at hrow
          rw [List.cons_append]
          rw [hrow]
          simp only [clauseKeys, List.map_cons, List.flatMap_cons, literalKey,
            Bool.toNat_false, Nat.add_zero, List.append_assoc]
          rw [ih (vertex := vertex + 1)]
          rfl

private theorem formula_rows (vertex clause : Nat) (formula : CNF)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom spec .vertex
        (encodeIndexedOccurrenceRowsFrom vertex clause formula ++ tail) =
      (formulaKeysFrom clause formula).flatMap encodeCliqueEdge ++
        rewriteStatefulFlatMapFrom spec .vertex tail := by
  induction formula generalizing vertex clause with
  | nil => rfl
  | cons literals formula ih =>
      simp only [encodeIndexedOccurrenceRowsFrom, formulaKeysFrom,
        List.flatMap_append, List.append_assoc]
      rw [clause_rows]
      rw [ih (vertex := vertex + literals.length) (clause := clause + 1)]

/-- The complete finite-state pass emits exactly the literal-key edge table
of the decoded formula, byte for byte. -/
theorem occurrenceKeyStream_encodeIndexedOccurrenceRows (formula : CNF) :
    occurrenceKeyStream (encodeIndexedOccurrenceRows formula) =
      (formulaKeys formula).flatMap encodeCliqueEdge := by
  unfold occurrenceKeyStream rewriteStatefulFlatMap
    encodeIndexedOccurrenceRows formulaKeys
  change rewriteStatefulFlatMapFrom spec .vertex
      (encodeIndexedOccurrenceRowsFrom 0 0 formula) =
    (formulaKeysFrom 0 formula).flatMap encodeCliqueEdge
  have h := formula_rows 0 0 formula []
  have hnil : rewriteStatefulFlatMapFrom spec .vertex [] = [] := rfl
  rw [hnil] at h
  simpa only [List.append_nil] using h

def canonicalOccurrenceKeys (input : List CNFSym) : List (Nat × Nat) :=
  formulaKeys (decodeCNF input)

theorem occurrenceKeyStream_canonical (input : List CNFSym) :
    occurrenceKeyStream (canonicalIndexedOccurrenceRows input) =
      (canonicalOccurrenceKeys input).flatMap encodeCliqueEdge := by
  exact occurrenceKeyStream_encodeIndexedOccurrenceRows (decodeCNF input)

def canonicalOccurrenceKeyStream (input : List CNFSym) : List CliqueSym :=
  (canonicalOccurrenceKeys input).flatMap encodeCliqueEdge

/-- End-to-end native polynomial-time generation of the literal-key edge
table from the raw CLRS 3-CNF word. -/
noncomputable def canonicalOccurrenceKeyStream_computableInPolyTime :
    TM2ComputableInPolyTime id id canonicalOccurrenceKeyStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    canonicalIndexedOccurrenceRows_computableInPolyTime
    occurrenceKeyStream_computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simp only [Function.comp_apply, id_eq] at output
        rw [occurrenceKeyStream_canonical] at output
        simpa [canonicalOccurrenceKeyStream] using output }

end PricingWithTips.FixedShapeOccurrenceKeysTM2


