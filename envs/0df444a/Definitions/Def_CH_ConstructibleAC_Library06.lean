-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library06
-- name    : CH_ConstructibleAC_Library06
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:08:32.934195+00:00
-- url     : https://prove2.me/theorems/f091f194-1c61-4f3c-91ca-8a5f641a43da
-- title:
--   Stack execution and constructible-model semantics
-- statement:
--   Finite stack programs and their traces have set-theoretic codes. This library provides the step-decoding and trace interfaces used to express their execution internally. It also introduces the membership language and the external constructible carrier, with the realization interfaces that connect set-theoretic definitions to first-order model assertions.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgramZFCode.lean#L1-L121; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackStepFormula.lean#L1-L409; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackStepDecode.lean#L1-L99; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/ModelTheory/SetTheory/Basic.lean#L1-L61; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Semantics.lean#L1-L86; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Model.lean#L1-L342; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FiniteSequenceComparison.lean#L1-L151; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/IndexedSequenceValidity.lean#L1-L252; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackTrace.lean#L1-L295

import Definitions.Def_CH_ConstructibleAC_Library05
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases

/-!
# Adaptation of Zike Liu's constructible-universe Choice proof

Original formalization: Copyright (c) 2026 Zike Liu, Apache-2.0.
Source: https://github.com/05-02-07/lean-constructible-universe
Commit: 7f5a7d03d63d9769172f17350bbe8303996e5b53.
All original per-file copyright notices are retained below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This credit concerns the Prove2Me adaptation and semantic bridge. The original
well-ordering formalization is by Zike Liu, credited above and in each source section.
-/

set_option autoImplicit false


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramZFCode -/
section CUAdapterModule28
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal codes for rudimentary stack programs

Postfix program tokens and whole instruction lists are encoded by genuine
`ZFSet`s.  Variable tokens carry their generator value; operation tokens carry
the finite ordinal operation index.  Whole programs use the indexed sequence
encoding, which is tailored to a first-order execution-trace predicate.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/-- Internal code of one postfix stack instruction. -/
def stackTokenZFCode (U : ZFSet.{u}) :
    StackToken (Option (Constructible.ZFCarrier U)) → ZFSet.{u}
  | .inl generator =>
      triple varTag (rudimentaryGenerator U generator) ∅
  | .inr operation =>
      triple appTag (operationCode operation) ∅

@[simp]
theorem stackTokenZFCode_variable (U : ZFSet.{u})
    (generator : Option (Constructible.ZFCarrier U)) :
    stackTokenZFCode U (.inl generator) =
      triple varTag (rudimentaryGenerator U generator) ∅ :=
  rfl

@[simp]
theorem stackTokenZFCode_operation (U : ZFSet.{u})
    (operation : Fin 9) :
    stackTokenZFCode U (.inr operation) =
      triple appTag (operationCode operation) ∅ :=
  rfl

/-- Internal stack-token codes retain the complete instruction. -/
theorem stackTokenZFCode_injective (U : ZFSet.{u}) :
    Function.Injective (stackTokenZFCode U) := by
  intro first second hcode
  cases first with
  | inl firstGenerator =>
      cases second with
      | inl secondGenerator =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with ⟨hgenerator, _hempty⟩
          exact congrArg Sum.inl
            (rudimentaryGenerator_injective U hgenerator)
      | inr secondOperation =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag)
  | inr firstOperation =>
      cases second with
      | inl secondGenerator =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag.symm)
      | inr secondOperation =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with
            ⟨hoperation, _hempty⟩
          exact congrArg Sum.inr
            (operationCode_injective hoperation)

/-- A whole postfix program, represented as an indexed finite sequence. -/
def stackProgramZFCode (U : ZFSet.{u})
    (program : List (StackToken
      (Option (Constructible.ZFCarrier U)))) : ZFSet.{u} :=
  IndexedSequenceZF.sequenceCode (program.map (stackTokenZFCode U))



/-- Every stack token code is constructible when its seed is. -/
theorem stackTokenZFCode_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U))) :
    stackTokenZFCode U token ∈ L := by
  cases token with
  | inl generator =>
      exact triple_mem_L varTag_mem_L
        (RudimentaryTerm.rudimentaryGenerator_mem_L hU generator)
        empty_mem_L
  | inr operation =>
      exact triple_mem_L appTag_mem_L
        (operationCode_mem_L operation) empty_mem_L

/-- Every finite postfix program has a constructible internal code. -/
theorem stackProgramZFCode_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (program : List (StackToken
      (Option (Constructible.ZFCarrier U)))) :
    stackProgramZFCode U program ∈ L := by
  apply IndexedSequenceZF.sequenceCode_mem_L
  intro encodedToken hEncodedToken
  rcases List.mem_map.mp hEncodedToken with ⟨token, _htoken, rfl⟩
  exact stackTokenZFCode_mem_L hU token

end

end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule28



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackStepFormula -/
section CUAdapterModule29
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order transition formula for rudimentary stack programs

The fixed parameter layout is

`[U, varTag, appTag, empty, op0, ..., op8, token, input, output]`.

The last three coordinates are the instruction and the two stack states.  A
variable instruction pushes its generator.  An operation instruction pops the
right and left operands, applies the selected Gödel operation, and pushes the
result.  Stack states use `FiniteSequenceZF.listCode`, whose cons constructor
is precisely a Kuratowski pair.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open Constructible.Delta0Formula

/-! ## Fixed indices -/

/-- The universe coordinate in the stack-step layout. -/
def stackStepUniverseIndex : Fin 16 := 0
/-- The variable-tag coordinate in the stack-step layout. -/
def stackStepVarTagIndex : Fin 16 := 1
/-- The application-tag coordinate in the stack-step layout. -/
def stackStepAppTagIndex : Fin 16 := 2
/-- The empty-stack coordinate in the stack-step layout. -/
def stackStepEmptyIndex : Fin 16 := 3
/-- The token coordinate in the stack-step layout. -/
def stackStepTokenIndex : Fin 16 := 13
/-- The input-stack coordinate in the stack-step layout. -/
def stackStepInputIndex : Fin 16 := 14
/-- The output-stack coordinate in the stack-step layout. -/
def stackStepOutputIndex : Fin 16 := 15

/-- The coordinate of the given rudimentary operation in the stack-step layout. -/
def stackStepOperationIndex (i : Fin 9) : Fin 16 :=
  ⟨4 + i.1, by omega⟩

/-- Lift an original free-variable index through one appended witness. -/
def stackStepLiftOne (i : Fin 16) : Fin 17 :=
  i.castSucc

/-- Lift an original free-variable index through five appended witnesses. -/
def stackStepLiftFive (i : Fin 16) : Fin 21 :=
  i.castSucc.castSucc.castSucc.castSucc.castSucc

/-- Select `[result,left,right]` in the five-witness operation context. -/
def stackStepOpGraphRename : Fin 3 → Fin 21 :=
  ![(19 : Fin 21), (17 : Fin 21), (16 : Fin 21)]

theorem comp_stackStepOpGraphRename {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    (fun i => snoc (snoc (snoc (snoc (snoc s right) left) rest)
      result) inner (stackStepOpGraphRename i)) =
      ![result, left, right] := by
  funext i
  fin_cases i <;> rfl

/-! ## Variable and operation branches -/

/-- The variable-token transition branch. -/
def variableStackStepFormula : FOFormula 16 :=
  .ex
    (.conj
      (Delta0Formula.tripleEqAt
        (stackStepLiftOne stackStepTokenIndex)
        (stackStepLiftOne stackStepVarTagIndex)
        (Fin.last 16)
        (stackStepLiftOne stackStepEmptyIndex)).toFO
      (.conj
        (FOFormula.disj
          (.eq (Fin.last 16)
            (stackStepUniverseIndex.castSucc))
          (.mem (Fin.last 16)
            (stackStepUniverseIndex.castSucc)))
        (Delta0Formula.kuratowskiPairEqAt
          (stackStepOutputIndex.castSucc)
          (Fin.last 16)
          (stackStepInputIndex.castSucc)).toFO))

/--
The operation branch for one of the nine operation indices.  The witnesses,
in order, are `right`, `left`, `rest`, `result`, and the inner input-stack
cell.
-/
def operationStackStepBody (i : Fin 9) : FOFormula 21 :=
  .conj
    (Delta0Formula.tripleEqAt
      (stackStepLiftFive stackStepTokenIndex)
      (stackStepLiftFive stackStepAppTagIndex)
      (stackStepLiftFive (stackStepOperationIndex i))
      (stackStepLiftFive stackStepEmptyIndex)).toFO
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (stackStepLiftFive stackStepInputIndex)
        (16 : Fin 21) (20 : Fin 21)).toFO
      (.conj
        (Delta0Formula.kuratowskiPairEqAt
          (20 : Fin 21) (17 : Fin 21) (18 : Fin 21)).toFO
        (.conj
          (Delta0Formula.kuratowskiPairEqAt
            (stackStepLiftFive stackStepOutputIndex)
            (19 : Fin 21) (18 : Fin 21)).toFO
          (FOFormula.rename stackStepOpGraphRename
            (opGraphFormula i).toFO))))

/-- The stack-step formula for one rudimentary operation. -/
def operationStackStepFormula (i : Fin 9) : FOFormula 16 :=
  .ex (.ex (.ex (.ex (.ex (operationStackStepBody i)))))

/-- A finite disjunction over all nine operation branches. -/
def anyOperationStackStepFormula : FOFormula 16 :=
  FOFormula.disj (operationStackStepFormula 0)
    (FOFormula.disj (operationStackStepFormula 1)
      (FOFormula.disj (operationStackStepFormula 2)
        (FOFormula.disj (operationStackStepFormula 3)
          (FOFormula.disj (operationStackStepFormula 4)
            (FOFormula.disj (operationStackStepFormula 5)
              (FOFormula.disj (operationStackStepFormula 6)
                (FOFormula.disj (operationStackStepFormula 7)
                  (operationStackStepFormula 8))))))))

/-- The complete fixed one-step transition formula. -/
def stackStepFormula : FOFormula 16 :=
  FOFormula.disj variableStackStepFormula anyOperationStackStepFormula

/-! ## Assignments and semantics -/

/-- The thirteen parameters shared by every stack-step assignment. -/
noncomputable def stackStepPrefixAssignment (U : ZFSet.{u}) :
    Tuple ZFSet.{u} 13 :=
  ![U, varTag, appTag, ∅,
    operationCode 0, operationCode 1, operationCode 2,
    operationCode 3, operationCode 4, operationCode 5,
    operationCode 6, operationCode 7, operationCode 8]

/-- The intended assignment to the fixed transition context. -/
noncomputable def stackStepAssignment (U token input output : ZFSet.{u}) :
    Tuple ZFSet.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixAssignment U) token) input) output

@[simp]
theorem stackStepAssignment_operation
    (U token input output : ZFSet.{u}) (i : Fin 9) :
    stackStepAssignment U token input output (stackStepOperationIndex i) =
      operationCode i := by
  fin_cases i <;> rfl

@[simp] theorem stackStepAssignment_appTag
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepAppTagIndex = appTag :=
  rfl

@[simp] theorem stackStepAssignment_empty
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepEmptyIndex = ∅ :=
  rfl

@[simp] theorem stackStepAssignment_token
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepTokenIndex = token :=
  rfl

@[simp] theorem stackStepAssignment_input
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepInputIndex = input :=
  rfl

@[simp] theorem stackStepAssignment_output
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepOutputIndex = output :=
  rfl

@[simp] theorem stackStepWitness_right {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (16 : Fin 21) = right :=
  rfl

@[simp] theorem stackStepWitness_left {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (17 : Fin 21) = left :=
  rfl

@[simp] theorem stackStepWitness_rest {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (18 : Fin 21) = rest :=
  rfl

@[simp] theorem stackStepWitness_result {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (19 : Fin 21) = result :=
  rfl

@[simp] theorem stackStepWitness_inner {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (20 : Fin 21) = inner :=
  rfl

@[simp]
theorem satisfies_variableStackStepFormula
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem variableStackStepFormula
        (stackStepAssignment U token input output) ↔
      ∃ generator : ZFSet.{u},
        token = triple varTag generator ∅ ∧
          (generator = U ∨ generator ∈ U) ∧
          output = ZFSet.pair generator input := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc,
    stackStepAssignment, stackStepLiftOne,
    stackStepTokenIndex, stackStepVarTagIndex,
    stackStepEmptyIndex, stackStepUniverseIndex,
    stackStepOutputIndex, stackStepInputIndex]
  rfl

@[simp]
theorem satisfies_operationStackStepFormula (i : Fin 9)
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem (operationStackStepFormula i)
        (stackStepAssignment U token input output) ↔
      ∃ right left rest result : ZFSet.{u},
        token = triple appTag (operationCode i) ∅ ∧
          input = ZFSet.pair right (ZFSet.pair left rest) ∧
          output = ZFSet.pair result rest ∧
          result = op i left right := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_rename,
    snoc_castSucc,
    stackStepLiftFive,
    stackStepAssignment_operation,
    stackStepAssignment_appTag, stackStepAssignment_empty,
    stackStepAssignment_token, stackStepAssignment_input,
    stackStepAssignment_output,
    stackStepWitness_right, stackStepWitness_left,
    stackStepWitness_rest, stackStepWitness_result,
    stackStepWitness_inner]
  constructor
  · rintro ⟨right, left, rest, result, inner,
      htoken, hinput, hinner, houtput, hop⟩
    have hop' : result = op i left right := by
      rw [comp_stackStepOpGraphRename] at hop
      exact (satisfies_opGraphFormula i result left right).mp hop
    exact ⟨right, left, rest, result, htoken,
      hinput.trans (congrArg (ZFSet.pair right) hinner),
      houtput, hop'⟩
  · rintro ⟨right, left, rest, result,
      htoken, hinput, houtput, hop⟩
    have hop' :
        Delta0Formula.Satisfies ZFMem (opGraphFormula i)
          ![result, left, right] :=
      (satisfies_opGraphFormula i result left right).mpr hop
    refine ⟨right, left, rest, result, ZFSet.pair left rest,
      htoken, hinput, rfl, houtput, ?_⟩
    simpa only [comp_stackStepOpGraphRename] using hop'

@[simp]
theorem satisfies_anyOperationStackStepFormula
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem anyOperationStackStepFormula
        (stackStepAssignment U token input output) ↔
      ∃ i : Fin 9, ∃ right left rest result : ZFSet.{u},
        token = triple appTag (operationCode i) ∅ ∧
          input = ZFSet.pair right (ZFSet.pair left rest) ∧
          output = ZFSet.pair result rest ∧
          result = op i left right := by
  simp only [anyOperationStackStepFormula, FOFormula.satisfies_disj,
    satisfies_operationStackStepFormula]
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
    · exact ⟨7, h⟩
    · exact ⟨8, h⟩
  · rintro ⟨i, h⟩
    fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h)))))))

/-- Raw semantic normal form of the complete transition formula. -/
@[simp]
theorem satisfies_stackStepFormula
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem stackStepFormula
        (stackStepAssignment U token input output) ↔
      (∃ generator : ZFSet.{u},
        token = triple varTag generator ∅ ∧
          (generator = U ∨ generator ∈ U) ∧
          output = ZFSet.pair generator input) ∨
      (∃ i : Fin 9, ∃ right left rest result : ZFSet.{u},
        token = triple appTag (operationCode i) ∅ ∧
          input = ZFSet.pair right (ZFSet.pair left rest) ∧
          output = ZFSet.pair result rest ∧
          result = op i left right) := by
  simp only [stackStepFormula, FOFormula.satisfies_disj,
    satisfies_variableStackStepFormula,
    satisfies_anyOperationStackStepFormula]

@[simp]
theorem listCode_eq_pair_iff (xs : List ZFSet.{u}) (x : ZFSet.{u})
    (rest : List ZFSet.{u}) :
    FiniteSequenceZF.listCode xs =
        ZFSet.pair x (FiniteSequenceZF.listCode rest) ↔
      xs = x :: rest := by
  rw [← FiniteSequenceZF.listCode_cons,
    FiniteSequenceZF.listCode_inj]

@[simp]
theorem pair_eq_listCode_iff (x : ZFSet.{u}) (rest xs : List ZFSet.{u}) :
    ZFSet.pair x (FiniteSequenceZF.listCode rest) =
        FiniteSequenceZF.listCode xs ↔
      xs = x :: rest := by
  rw [eq_comm, listCode_eq_pair_iff]

theorem zfPair_ne_empty (x y : ZFSet.{u}) :
    ZFSet.pair x y ≠ ∅ := by
  intro h
  have hx : ({x} : ZFSet.{u}) ∈ ZFSet.pair x y := by
    simp [ZFSet.pair]
  rw [h] at hx
  exact ZFSet.notMem_empty _ hx

@[simp]
theorem empty_ne_zfPair (x y : ZFSet.{u}) :
    (∅ : ZFSet.{u}) ≠ ZFSet.pair x y :=
  (zfPair_ne_empty x y).symm

@[simp, nolint simpNF]
theorem appTag_ne_varTag : (appTag : ZFSet.{u}) ≠ varTag :=
  varTag_ne_appTag.symm

/-- On genuine token and stack codes, the formula is exactly one machine step. -/
theorem satisfies_stackStepFormula_iff_run
    (U : ZFSet.{u})
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u}) :
    FOFormula.Satisfies ZFMem stackStepFormula
        (stackStepAssignment U (stackTokenZFCode U token)
          (FiniteSequenceZF.listCode input)
          (FiniteSequenceZF.listCode output)) ↔
      runStackToken (rudimentaryGenerator U) token input = some output := by
  cases token with
  | inl generator =>
      cases generator <;>
        simp [satisfies_stackStepFormula, stackTokenZFCode,
          runStackToken, rudimentaryGenerator, triple, ZFSet.pair_inj,
          eq_comm]
  | inr operation =>
      cases input with
      | nil =>
          simp [satisfies_stackStepFormula, stackTokenZFCode,
            runStackToken, triple, ZFSet.pair_inj,
            appTag_ne_varTag, operationCode_injective.eq_iff,
            empty_ne_zfPair]
      | cons right tail =>
          cases tail with
          | nil =>
              simp [satisfies_stackStepFormula, stackTokenZFCode,
                runStackToken, triple, ZFSet.pair_inj,
                appTag_ne_varTag, operationCode_injective.eq_iff,
                empty_ne_zfPair]
          | cons left rest =>
              simp [satisfies_stackStepFormula, stackTokenZFCode,
                runStackToken, triple, ZFSet.pair_inj,
                appTag_ne_varTag, operationCode_injective.eq_iff,
                eq_comm]

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule29



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackStepDecode -/
section CUAdapterModule30
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Decoding arbitrary satisfying stack-step codes

The basic semantic theorem for `stackStepFormula` was first stated on genuine
token and stack codes.  Whole-program soundness also needs the converse shape:
starting from a genuine input stack code, every arbitrary raw token/output pair
accepted by the formula must decode to a real instruction and a real output
stack.  This file proves exactly that fact.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

/--
With a genuine input stack code, one-step satisfaction is equivalent to the
existence of a genuine token and output stack producing the supplied raw codes.
-/
theorem satisfies_stackStepFormula_iff_exists_decoding
    (U tokenCode outputCode : ZFSet.{u}) (input : List ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U tokenCode (listCode input) outputCode) ↔
      ∃ token : StackToken (Option (Constructible.ZFCarrier U)),
        ∃ output : List ZFSet.{u},
          tokenCode = stackTokenZFCode U token ∧
            outputCode = listCode output ∧
            runStackToken (rudimentaryGenerator U) token input = some output := by
  constructor
  · intro hsatisfies
    rw [satisfies_stackStepFormula] at hsatisfies
    rcases hsatisfies with hvariable | hoperation
    · rcases hvariable with
        ⟨generator, htoken, hgenerator, houtput⟩
      rcases hgenerator with hgeneratorEq | hgeneratorMem
      · subst generator
        refine ⟨.inl none, U :: input, ?_, ?_, rfl⟩
        · simpa only [stackTokenZFCode_variable,
            rudimentaryGenerator] using htoken
        · simpa only [listCode_cons] using houtput
      · let generatorCarrier : Constructible.ZFCarrier U :=
          ⟨generator, hgeneratorMem⟩
        refine ⟨.inl (some generatorCarrier), generator :: input,
          ?_, ?_, rfl⟩
        · simpa only [stackTokenZFCode_variable,
            rudimentaryGenerator, generatorCarrier] using htoken
        · simpa only [listCode_cons] using houtput
    · rcases hoperation with
        ⟨operation, right, left, rest, result,
          htoken, hinput, houtput, hresult⟩
      cases input with
      | nil =>
          exact False.elim (empty_ne_zfPair right (ZFSet.pair left rest) hinput)
      | cons first tail =>
          have hfirst := (ZFSet.pair_inj.mp hinput).1
          have htail := (ZFSet.pair_inj.mp hinput).2
          subst first
          cases tail with
          | nil =>
              exact False.elim (empty_ne_zfPair left rest htail)
          | cons second remaining =>
              have hsecond := (ZFSet.pair_inj.mp htail).1
              have hremaining := (ZFSet.pair_inj.mp htail).2
              subst second
              rw [← hremaining] at houtput
              subst result
              refine ⟨.inr operation,
                op operation left right :: remaining, ?_, ?_, rfl⟩
              · simpa only [stackTokenZFCode_operation] using htoken
              · simpa only [listCode_cons] using houtput
  · rintro ⟨token, output, rfl, rfl, hrun⟩
    exact (satisfies_stackStepFormula_iff_run U token input output).mpr hrun

/-- The forward decoding direction as a convenient standalone lemma. -/
theorem exists_decoding_of_satisfies_stackStepFormula
    (U tokenCode outputCode : ZFSet.{u}) (input : List ZFSet.{u})
    (hsatisfies :
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U tokenCode (listCode input) outputCode)) :
    ∃ token : StackToken (Option (Constructible.ZFCarrier U)),
      ∃ output : List ZFSet.{u},
        tokenCode = stackTokenZFCode U token ∧
          outputCode = listCode output ∧
          runStackToken (rudimentaryGenerator U) token input = some output :=
  (satisfies_stackStepFormula_iff_exists_decoding
    U tokenCode outputCode input).mp hsatisfies

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule30



/- Original module: ConstructibleUniverse.ModelTheory.SetTheory.Basic -/
section CUAdapterModule31
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# The First-Order Language of Set Theory

This file defines the first-order language with a single binary relation symbol
for membership. Equality is provided by first-order logic itself.

## Main Definitions

- `FirstOrder.Language.setTheory` is the first-order language of set theory.
- `FirstOrder.Language.Term.mem` is the atomic formula asserting membership between two terms.
- `FirstOrder.Language.setTheoryStructure` interprets membership as a binary relation.
-/


universe u v

namespace FirstOrder.Language

open Structure

variable {M : Type u} {α : Type v} {n : ℕ}

/-- The relation symbols of the first-order language of set theory. -/
inductive setTheoryRel : ℕ → Type
  | mem : setTheoryRel 2
  deriving DecidableEq

/-- The relational language with a single binary relation symbol for membership. -/
protected def setTheory : Language :=
  ⟨fun _ => Empty, setTheoryRel⟩
  deriving IsRelational

/-- The membership relation symbol in the first-order language of set theory. -/
abbrev memRel : Language.setTheory.Relations 2 := .mem

/-- The atomic formula asserting that `t₁` is a member of `t₂`. -/
def Term.mem (t₁ t₂ : Language.setTheory.Term (α ⊕ Fin n)) :
    Language.setTheory.BoundedFormula α n :=
  memRel.boundedFormula₂ t₁ t₂

/-- Interpret the first-order language of set theory using a binary relation. -/
@[implicit_reducible]
def setTheoryStructure (r : M → M → Prop) : Language.setTheory.Structure M where
  RelMap | .mem => fun x ↦ r (x 0) (x 1)

@[simp]
theorem setTheoryStructure_relMap (r : M → M → Prop) (x : Fin 2 → M) :
    @RelMap Language.setTheory M (setTheoryStructure r) 2 memRel x ↔ r (x 0) (x 1) :=
  Iff.rfl

end FirstOrder.Language
end CUAdapterModule31



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Semantics -/
section CUAdapterModule32
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# Semantics for formulas in the language of set theory

This file provides relation-parametric term evaluation and formula realization
for Mathlib's first-order language of set theory.

The relation-parametric semantics below uses `BoundedFormula Empty n`: there are no
named free variables, and the `n` variables currently in scope are interpreted
by an assignment `Fin n -> A`.
-/


universe u

namespace Constructible

namespace Model

/-- Evaluate a term under an assignment in the membership structure induced by `E`. -/
def termValue {A : Type u} (E : A -> A -> Prop) {n : Nat}
    (t : FirstOrder.Language.setTheory.Term (Sum Empty (Fin n)))
    (s : Fin n -> A) : A :=
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  t.realize (Sum.elim Empty.elim s)

/-- Realization in the membership structure induced by `E`. -/
def realizes {A : Type u} (E : A -> A -> Prop) {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty n)
    (s : Fin n -> A) : Prop :=
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  phi.Realize Empty.elim s

theorem realizes_falsum {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {s : Fin n -> A} :
    realizes E (.falsum : FirstOrder.Language.setTheory.BoundedFormula Empty n) s <-> False := by
  rfl





theorem realizes_imp {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {phi psi : FirstOrder.Language.setTheory.BoundedFormula Empty n}
    {s : Fin n -> A} :
    realizes E (phi.imp psi) s <->
      (realizes E phi s -> realizes E psi s) := by
  rfl

theorem realizes_all {A : Type u} {E : A -> A -> Prop}
    {n : Nat} {phi : FirstOrder.Language.setTheory.BoundedFormula Empty (n + 1)}
    {s : Fin n -> A} :
    realizes E phi.all s <->
      forall x : A, realizes E phi (Fin.snoc s x) := by
  rfl



end Model

end Constructible
end CUAdapterModule32



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Model -/
section CUAdapterModule33
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The first-order structure carried by the constructible universe

This file connects the formula syntax used to construct `L` with Mathlib's
general model-theory API.  The language has no function symbols and one binary
relation symbol, interpreted as membership.

The existing `Constructible.FOFormula n` treats all `n` variables uniformly
and appends a bound variable at the end of a tuple.  Mathlib's
`BoundedFormula Empty n` has exactly the same convention, so the translation
below does not need a variable permutation.
-/


open Set

universe u

namespace Constructible

namespace Model

/-! ## Raw-domain semantics for external classes -/

/--
Satisfaction with quantifiers restricted to an external class of `ZFSet`s.

Assignments remain raw `ZFSet` tuples.  This is the useful presentation for
comparing two domains such as `LStageZF alpha` and `L`, since the same tuple can
be passed to both sides without transporting subtype values.
-/
@[simp]
def SatisfiesIn (M : Set ZFSet.{u}) :
    {n : Nat} -> FOFormula n -> Tuple ZFSet.{u} n -> Prop
  | _, .mem i j, s => s i ∈ s j
  | _, .eq i j, s => s i = s j
  | _, .neg phi, s => ¬SatisfiesIn M phi s
  | _, .conj phi psi, s => SatisfiesIn M phi s ∧ SatisfiesIn M psi s
  | _, .ex phi, s => ∃ x, x ∈ M ∧ SatisfiesIn M phi (snoc s x)

/-- The subtype whose elements range over an external class `M`. -/
abbrev ClassCarrier (M : Set ZFSet.{u}) := {x : ZFSet.{u} // x ∈ M}

theorem subtypeVal_snoc {M : Set ZFSet.{u}} {n : Nat}
    (s : Tuple (ClassCarrier M) n) (x : ClassCarrier M) :
    (fun i => (snoc s x i).1) = snoc (fun i => (s i).1) x.1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/--
Raw-domain restricted satisfaction is equivalent to ordinary satisfaction on
the subtype carrying exactly the elements of `M`.
-/
theorem satisfies_subtype_iff_satisfiesIn (M : Set ZFSet.{u}) {n : Nat}
    (phi : FOFormula n) (s : Tuple (ClassCarrier M) n) :
    FOFormula.Satisfies
        (fun x y : ClassCarrier M => x.1 ∈ y.1) phi s ↔
      SatisfiesIn M phi (fun i => (s i).1) := by
  induction phi with
  | mem i j => rfl
  | eq i j =>
      constructor
      · exact fun h => congrArg Subtype.val h
      · exact fun h => Subtype.ext h
  | neg phi ih => exact not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x.1, x.2, ?_⟩
        simpa only [subtypeVal_snoc] using (ih (snoc s x)).mp hx
      · rintro ⟨x, hxM, hx⟩
        let xM : ClassCarrier M := ⟨x, hxM⟩
        refine ⟨xM, (ih (snoc s xM)).mpr ?_⟩
        simpa only [subtypeVal_snoc] using hx

/-- The ambient `ZFSet` universe, regarded as a membership structure. -/
instance zfSetMembershipStructure :
    FirstOrder.Language.setTheory.Structure ZFSet.{u} :=
  FirstOrder.Language.setTheoryStructure fun x y => x ∈ y

/-- The type of constructible sets.  Its membership proof is part of the type. -/
abbrev LCarrier := ClassCarrier (L : Set ZFSet.{u})

/-- Membership on the constructible carrier, inherited from `ZFSet`. -/
abbrev lCarrierMem (x y : LCarrier.{u}) : Prop := x.1 ∈ y.1

/-- The type of elements of one constructible stage. -/
abbrev StageCarrier (alpha : Ordinal.{u}) :=
  ClassCarrier (LStageZF alpha : Set ZFSet.{u})

/-- The subtype/raw-domain bridge specialized to the full constructible class. -/
theorem satisfies_lCarrier_iff_satisfiesIn_L {n : Nat} (phi : FOFormula n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun x y : LCarrier.{u} => x.1 ∈ y.1) phi s ↔
      SatisfiesIn (L : Set ZFSet.{u}) phi (fun i => (s i).1) :=
  satisfies_subtype_iff_satisfiesIn (L : Set ZFSet.{u}) phi s

/-- The subtype/raw-domain bridge specialized to a constructible stage. -/
theorem satisfies_stageCarrier_iff_satisfiesIn {alpha : Ordinal.{u}}
    {n : Nat} (phi : FOFormula n) (s : Tuple (StageCarrier alpha) n) :
    FOFormula.Satisfies
        (fun x y : StageCarrier alpha => x.1 ∈ y.1) phi s ↔
      SatisfiesIn (LStageZF alpha : Set ZFSet.{u}) phi
        (fun i => (s i).1) :=
  satisfies_subtype_iff_satisfiesIn
    (LStageZF alpha : Set ZFSet.{u}) phi s

/-- Membership on `LCarrier` is ambient membership restricted to `L`. -/
instance lCarrierMembershipStructure :
    FirstOrder.Language.setTheory.Structure LCarrier.{u} :=
  FirstOrder.Language.setTheoryStructure lCarrierMem

/--
Translate the construction syntax to Mathlib's bounded-formula syntax.

All variables of `FOFormula n` become Mathlib bound variables.  This gives a
sentence when `n = 0` and supports the existing last-variable quantifier
convention for arbitrary `n`.
-/
def toBoundedFormula : {n : Nat} -> FOFormula n ->
    FirstOrder.Language.setTheory.BoundedFormula Empty n
  | _, .mem i j =>
      FirstOrder.Language.Term.mem (.var (Sum.inr i)) (.var (Sum.inr j))
  | _, .eq i j =>
      .equal (.var (Sum.inr i)) (.var (Sum.inr j))
  | _, .neg phi => (toBoundedFormula phi).not
  | _, .conj phi psi => toBoundedFormula phi ⊓ toBoundedFormula psi
  | _, .ex phi => (toBoundedFormula phi).ex

/-- Extract the index denoted by a term in the function-free membership language. -/
def fromBoundedTerm {n : Nat} :
    FirstOrder.Language.setTheory.Term (Empty ⊕ Fin n) -> Fin n
  | .var (Sum.inl i) => Empty.elim i
  | .var (Sum.inr i) => i
  | .func f _ => Empty.elim f

/--
Normalize a Mathlib membership-language formula to the small construction
syntax.  The two syntaxes use different primitive Boolean connectives, but
they have the same expressive power.
-/
def fromBoundedFormula : {n : Nat} ->
    FirstOrder.Language.setTheory.BoundedFormula Empty n -> FOFormula n
  | n, .falsum => .ex (.neg (.eq (Fin.last n) (Fin.last n)))
  | _, .equal t u => .eq (fromBoundedTerm t) (fromBoundedTerm u)
  | _, .rel .mem ts =>
      .mem (fromBoundedTerm (ts 0)) (fromBoundedTerm (ts 1))
  | _, .imp phi psi =>
      FOFormula.disj (.neg (fromBoundedFormula phi))
        (fromBoundedFormula psi)
  | _, .all phi => FOFormula.all (fromBoundedFormula phi)



theorem snoc_eq_finSnoc {A : Type u} {n : Nat}
    (s : Fin n -> A) (x : A) : snoc s x = Fin.snoc s x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

section ArbitraryStructure

variable {A : Type u} (E : A -> A -> Prop)

@[simp]
theorem termValue_eq_assignment {n : Nat}
    (t : FirstOrder.Language.setTheory.Term (Empty ⊕ Fin n)) (s : Fin n -> A) :
    termValue E t s = s (fromBoundedTerm t) := by
  cases t with
  | var i =>
      cases i with
      | inl i => exact Empty.elim i
      | inr i => rfl
  | func f _ => exact Empty.elim f

/-- Realization of a translated formula with an explicitly supplied relation. -/
def translatedRealizes {n : Nat} (phi : FOFormula n) (s : Tuple A n) : Prop :=
  realizes E (toBoundedFormula phi) s

/--
The translation preserves Tarskian satisfaction in every binary structure.
In particular, this applies both to ambient `ZFSet` and to `LCarrier`.
-/
@[simp]
theorem realize_toBoundedFormula {n : Nat} (phi : FOFormula n)
    (s : Tuple A n) :
    translatedRealizes E phi s ↔
      FOFormula.Satisfies E phi s := by
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  induction phi with
  | mem i j =>
      change E (s i) (s j) ↔ E (s i) (s j)
      rfl
  | eq i j =>
      change s i = s j ↔ s i = s j
      rfl
  | neg phi ih =>
      change (¬translatedRealizes E phi s) ↔
        ¬FOFormula.Satisfies E phi s
      exact not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      change
        ((toBoundedFormula phi ⊓ toBoundedFormula psi).Realize Empty.elim s) ↔
          FOFormula.Satisfies E phi s ∧ FOFormula.Satisfies E psi s
      rw [FirstOrder.Language.BoundedFormula.realize_inf]
      exact and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      change
        ((toBoundedFormula phi).ex.Realize Empty.elim s) ↔
          ∃ x, FOFormula.Satisfies E phi (snoc s x)
      rw [FirstOrder.Language.BoundedFormula.realize_ex]
      simp only [snoc_eq_finSnoc]
      exact exists_congr fun x => ih (Fin.snoc s x)



/--
Every Mathlib formula in the function-free membership language has the same
semantics as its normalization to `FOFormula`.
-/
@[simp]
theorem realize_fromBoundedFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty n)
    (s : Tuple A n) :
    realizes E phi s <->
      FOFormula.Satisfies E (fromBoundedFormula phi) s := by
  classical
  induction phi with
  | falsum =>
      rw [realizes_falsum]
      simp only [fromBoundedFormula]
      simp [FOFormula.Satisfies]
  | equal t u =>
      change termValue E t s = termValue E u s <->
        s (fromBoundedTerm t) = s (fromBoundedTerm u)
      rw [termValue_eq_assignment, termValue_eq_assignment]
  | rel R ts =>
      cases R with
      | mem =>
          change E (termValue E (ts 0) s) (termValue E (ts 1) s) <->
            E (s (fromBoundedTerm (ts 0)))
              (s (fromBoundedTerm (ts 1)))
          rw [termValue_eq_assignment, termValue_eq_assignment]
  | imp phi psi ihPhi ihPsi =>
      rw [realizes_imp]
      simp only [fromBoundedFormula]
      rw [FOFormula.satisfies_disj]
      change (realizes E phi s -> realizes E psi s) <->
        Not (FOFormula.Satisfies E (fromBoundedFormula phi) s) \/
          FOFormula.Satisfies E (fromBoundedFormula psi) s
      rw [ihPhi, ihPsi]
      tauto
  | all phi ih =>
      rw [realizes_all]
      simp only [fromBoundedFormula]
      rw [FOFormula.satisfies_all]
      simp only [snoc_eq_finSnoc]
      change (forall x : A, realizes E phi (Fin.snoc s x)) <->
        forall x : A,
          FOFormula.Satisfies E (fromBoundedFormula phi) (Fin.snoc s x)
      exact forall_congr' fun x => ih (Fin.snoc s x)



end ArbitraryStructure

/-!
## `DefZF` through Mathlib formulas
-/

/--
The internal definable-powerset operation is characterized by Mathlib's
membership-language formulas and by the intrinsically scoped `FOFormula`
syntax.
-/
theorem mem_DefZF_iff_exists_realizes {a z : ZFSet.{u}} :
    z ∈ DefZF a <->
      z ⊆ a /\
        Exists fun n : Nat =>
          Exists fun s : Tuple (ZFCarrier a) n =>
            Exists fun phi :
              FirstOrder.Language.setTheory.BoundedFormula Empty (n + 1) =>
              forall x : ZFCarrier a,
                x.1 ∈ z <->
                  realizes (zfCarrierMem a) phi (snoc s x) := by
  rw [mem_DefZF_iff_exists_satisfies]
  constructor
  · rintro ⟨hza, n, s, phi, hphi⟩
    refine ⟨hza, n, s, toBoundedFormula phi, ?_⟩
    intro x
    have hsem :=
      realize_toBoundedFormula (zfCarrierMem a) phi (snoc s x)
    exact (hphi x).trans (by
      simpa [translatedRealizes] using hsem.symm)
  · rintro ⟨hza, n, s, phi, hphi⟩
    refine ⟨hza, n, s, fromBoundedFormula phi, ?_⟩
    intro x
    exact (hphi x).trans
      (realize_fromBoundedFormula (zfCarrierMem a) phi (snoc s x))

/-- The specialized satisfaction bridge for the constructible universe. -/
@[simp]
theorem lCarrier_realize_toBoundedFormula {n : Nat} (phi : FOFormula n)
    (s : Tuple LCarrier.{u} n) :
    (toBoundedFormula phi).Realize Empty.elim s ↔
      FOFormula.Satisfies (fun x y : LCarrier.{u} => x.1 ∈ y.1) phi s :=
  realize_toBoundedFormula (fun x y : LCarrier.{u} => x.1 ∈ y.1) phi s

end Model

end Constructible
end CUAdapterModule33



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteSequenceComparison -/
section CUAdapterModule34
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded comparison formulas for finite-sequence codes

The von Neumann codes used for lengths are ordered by membership, so their
strict comparison has a fixed atomic formula.  We also package the
lexicographic comparison of an operation token's three numeric components.

The equal-length branch of shortlex for `FiniteSequenceZF.sequenceCode` is
handled by the indexed-sequence validity and lookup infrastructure developed
in the companion modules.  The formulas below provide the reusable numeric
and lexicographic components used by those constructions.
-/


universe u

namespace Constructible

namespace FiniteSequenceZF

/-! ## Natural-number codes -/

/--
Strict comparison of two von Neumann natural-number codes.

The assignment layout is `[left,right]`; membership is strict ordinal order.
-/
def natCodeLtDelta0 : Delta0Formula 2 :=
  .mem 0 1

/-- The same comparison in the unrestricted syntax used by model semantics. -/
def natCodeLtFormula : FOFormula 2 :=
  natCodeLtDelta0.toFO

@[simp, nolint simpNF]
theorem natCode_mem_natCode_iff (m n : Nat) :
    (natCode m : ZFSet.{u}) ∈ natCode n ↔ m < n := by
  change (m : Ordinal.{u}).toZFSet ∈ (n : Ordinal.{u}).toZFSet ↔ m < n
  rw [Ordinal.toZFSet_mem_toZFSet_iff]
  exact_mod_cast Iff.rfl

@[simp]
theorem satisfies_natCodeLtDelta0 (m n : Nat) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natCodeLtDelta0
        ![(natCode m : ZFSet.{u}), natCode n] ↔
      m < n := by
  simp [natCodeLtDelta0]

@[simp]
theorem satisfies_natCodeLtFormula (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem natCodeLtFormula
        ![(natCode m : ZFSet.{u}), natCode n] ↔
      m < n := by
  rw [natCodeLtFormula, Delta0Formula.satisfies_toFO,
    satisfies_natCodeLtDelta0]

/-- A natural-number code bundled as an element of the constructible carrier. -/
noncomputable def natCodeLCarrier (n : Nat) : Model.LCarrier.{u} :=
  ⟨natCode n, natCode_mem_L n⟩

@[simp]
theorem satisfies_natCodeLtFormula_lCarrier (m n : Nat) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        natCodeLtFormula ![natCodeLCarrier m, natCodeLCarrier n] ↔
      m < n := by
  change (natCode m : ZFSet.{u}) ∈ natCode n ↔ m < n
  exact natCode_mem_natCode_iff m n

end FiniteSequenceZF

namespace Godel.RudimentaryTerm

/-! ## Numeric operation-token payloads -/

/-- Operation indices, like sequence lengths, are finite ordinal codes. -/
@[simp]
theorem operationCode_mem_operationCode_iff (i j : Fin 9) :
    (operationCode i : ZFSet.{u}) ∈ operationCode j ↔ i < j := by
  change (i.1 : Ordinal.{u}).toZFSet ∈
      (j.1 : Ordinal.{u}).toZFSet ↔ i < j
  rw [Ordinal.toZFSet_mem_toZFSet_iff]
  exact_mod_cast Iff.rfl

@[simp]
theorem operationCode_inj_iff (i j : Fin 9) :
    (operationCode i : ZFSet.{u}) = operationCode j ↔ i = j :=
  operationCode_injective.eq_iff

/--
Lexicographic comparison of two operation-token numeric payloads.

The assignment layout is
`[op,leftLength,rightLength,op',leftLength',rightLength']`.
-/
def operationTupleLexDelta0 : Delta0Formula 6 :=
  .disj
    (.mem 0 3)
    (.conj
      (.eq 0 3)
      (.disj
        (.mem 1 4)
        (.conj (.eq 1 4) (.mem 2 5))))

/-- The operation-token payload comparison in unrestricted syntax. -/
def operationTupleLexFormula : FOFormula 6 :=
  operationTupleLexDelta0.toFO

@[simp]
theorem satisfies_operationTupleLexDelta0
    (i j : Fin 9) (left right left' right' : Nat) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem operationTupleLexDelta0
        ![(operationCode i : ZFSet.{u}),
          FiniteSequenceZF.natCode left,
          FiniteSequenceZF.natCode right,
          operationCode j,
          FiniteSequenceZF.natCode left',
          FiniteSequenceZF.natCode right'] ↔
      operationTokenRel (i, left, right) (j, left', right') := by
  simp [operationTupleLexDelta0, operationTokenRel, Prod.lex_def]

@[simp]
theorem satisfies_operationTupleLexFormula
    (i j : Fin 9) (left right left' right' : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem operationTupleLexFormula
        ![(operationCode i : ZFSet.{u}),
          FiniteSequenceZF.natCode left,
          FiniteSequenceZF.natCode right,
          operationCode j,
          FiniteSequenceZF.natCode left',
          FiniteSequenceZF.natCode right'] ↔
      operationTokenRel (i, left, right) (j, left', right') := by
  rw [operationTupleLexFormula, Delta0Formula.satisfies_toFO,
    satisfies_operationTupleLexDelta0]

end Godel.RudimentaryTerm

end Constructible
end CUAdapterModule34



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity -/
section CUAdapterModule35
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Validity and decoding of indexed finite-sequence codes

The indexed representation is useful only if object-language predicates cannot
accept spurious infinite or non-functional graphs as finite programs.  This
file supplies a fixed first-order validity predicate and proves two
representation theorems:

* every genuine `sequenceCode xs` is valid;
* every valid code represents one actual finite Lean list.

The representing graph is allowed to contain irrelevant extra elements.  At
each index below the recorded length, however, it must contain exactly one
value. Every predicate consuming this representation inspects only those
indexed values, so this is the precise invariant required for sound decoding.
-/


universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF

/-! ## Natural members of omega and finite ordinals -/

/-- The members of the standard von Neumann omega are exactly `natCode`s. -/
theorem mem_omega_iff_exists_natCode (x : ZFSet.{u}) :
    x ∈ Ordinal.omega0.toZFSet ↔ ∃ n : Nat, x = natCode n := by
  constructor
  · intro hx
    rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, rfl⟩
    rcases Ordinal.lt_omega0.mp halpha with ⟨n, hn⟩
    subst alpha
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)

/-- Membership in a finite von Neumann ordinal is bounded natural indexing. -/
theorem mem_natCode_iff_exists_lt (x : ZFSet.{u}) (n : Nat) :
    x ∈ natCode n ↔ ∃ k : Nat, k < n ∧ x = natCode k := by
  constructor
  · intro hx
    rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, rfl⟩
    have halphaOmega : alpha < Ordinal.omega0 :=
      halpha.trans (Ordinal.natCast_lt_omega0 n)
    rcases Ordinal.lt_omega0.mp halphaOmega with ⟨k, hk⟩
    subst alpha
    have hkn : k < n := by
      exact_mod_cast halpha
    exact ⟨k, hkn, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (natCode_mem_natCode_iff k n).mpr hk

/-! ## The fixed first-order predicate -/

/-- With the supplied indices, assert that `<value,index>` belongs to `graph`. -/
def functionGraphValueAt {n : Nat} (graph value index : Fin n) :
    FOFormula n :=
  (Delta0Formula.boundedEx graph
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) value.castSucc index.castSucc)).toFO

@[simp]
theorem satisfies_functionGraphValueAt {n : Nat}
    (graph value index : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (functionGraphValueAt graph value index) s ↔
      ZFSet.pair (s value) (s index) ∈ s graph := by
  simp only [functionGraphValueAt, Delta0Formula.satisfies_toFO,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s value) (s index), hq, rfl⟩

/-- Formula-level implication, kept local to avoid importing theory packaging. -/
def formulaImp {n : Nat} (phi psi : FOFormula n) : FOFormula n :=
  FOFormula.disj (.neg phi) psi

@[simp]
theorem satisfies_formulaImp {A : Type u} (E : A → A → Prop)
    {n : Nat} (phi psi : FOFormula n) (s : Tuple A n) :
    FOFormula.Satisfies E (formulaImp phi psi) s ↔
      (FOFormula.Satisfies E phi s → FOFormula.Satisfies E psi s) := by
  rw [formulaImp, FOFormula.satisfies_disj]
  change (¬FOFormula.Satisfies E phi s ∨ FOFormula.Satisfies E psi s) ↔ _
  constructor
  · rintro (hphi | hpsi) h
    · exact False.elim (hphi h)
    · exact hpsi
  · intro h
    by_cases hphi : FOFormula.Satisfies E phi s
    · exact Or.inr (h hphi)
    · exact Or.inl hphi

/-
Assignment layout in the innermost context:

`[omega, sequence, length, graph, index, value, other]`.
-/

/-- At the current index, the graph has exactly one value. -/
def uniqueValueAtBody : FOFormula 6 :=
  .conj
    (functionGraphValueAt (3 : Fin 6) (5 : Fin 6) (4 : Fin 6))
    (.all
      (formulaImp
        (functionGraphValueAt (3 : Fin 7) (6 : Fin 7) (4 : Fin 7))
        (.eq (6 : Fin 7) (5 : Fin 7))))

/-- Every index in the recorded length has a unique graph value. -/
def totalFunctionalBody : FOFormula 5 :=
  formulaImp
    (.mem (4 : Fin 5) (2 : Fin 5))
    (.ex uniqueValueAtBody)

/--
`sequenceValidityFormula(omega, sequence)` says that `sequence` records a
natural length and a total, single-valued graph on that finite ordinal.
-/
def sequenceValidityFormula : FOFormula 2 :=
  .ex (.ex
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO
      (.conj
        (.mem (2 : Fin 4) (0 : Fin 4))
        (.all totalFunctionalBody))))

@[simp]
theorem satisfies_uniqueValueAtBody
    (omega sequence length graph index value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value index ∈ graph ∧
        ∀ other : ZFSet.{u},
          ZFSet.pair other index ∈ graph → other = value := by
  simp [uniqueValueAtBody, Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_totalFunctionalBody
    (omega sequence length graph index : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index ∈ length →
        ∃ value : ZFSet.{u},
          ZFSet.pair value index ∈ graph ∧
            ∀ other : ZFSet.{u},
              ZFSet.pair other index ∈ graph → other = value) := by
  simp [totalFunctionalBody, Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_sequenceValidityFormula
    (omega sequence : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![omega, sequence] ↔
      ∃ length graph : ZFSet.{u},
        sequence = ZFSet.pair length graph ∧
          length ∈ omega ∧
          ∀ index : ZFSet.{u}, index ∈ length →
            ∃ value : ZFSet.{u},
              ZFSet.pair value index ∈ graph ∧
                ∀ other : ZFSet.{u},
                  ZFSet.pair other index ∈ graph → other = value := by
  simp [sequenceValidityFormula, Model.snoc_eq_finSnoc]

/-! ## External representation and decoding -/

/-- A finite list is represented by the uniquely indexed part of a code. -/
def Represents (sequence : ZFSet.{u}) (xs : List ZFSet.{u}) : Prop :=
  ∃ graph : ZFSet.{u},
    sequence = ZFSet.pair (natCode xs.length) graph ∧
      ∀ k : Fin xs.length,
        ZFSet.pair (xs.get k) (natCode k.1) ∈ graph ∧
          ∀ value : ZFSet.{u},
            ZFSet.pair value (natCode k.1) ∈ graph → value = xs.get k

/-- A genuine indexed sequence code represents its source list. -/
theorem represents_sequenceCode (xs : List ZFSet.{u}) :
    Represents (sequenceCode xs) xs := by
  refine ⟨graph xs, rfl, ?_⟩
  intro k
  constructor
  · exact (mem_graph_iff xs _).mpr ⟨k, rfl⟩
  · intro value hvalue
    rcases (mem_graph_iff xs _).mp hvalue with ⟨j, hpair⟩
    have hparts := ZFSet.pair_inj.mp hpair
    have hindex : k.1 = j.1 := natCode_injective hparts.2
    have hkj : k = j := Fin.ext hindex
    subst j
    exact hparts.1

/-- Validity is precisely representability by some finite list. -/
theorem satisfies_sequenceValidityFormula_iff_exists_represents
    (sequence : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![Ordinal.omega0.toZFSet, sequence] ↔
      ∃ xs : List ZFSet.{u}, Represents sequence xs := by
  rw [satisfies_sequenceValidityFormula]
  constructor
  · rintro ⟨length, graph, hsequence, hlength, hfunctional⟩
    rcases (mem_omega_iff_exists_natCode length).mp hlength with
      ⟨n, rfl⟩
    have hvalue : ∀ k : Fin n, ∃ value : ZFSet.{u},
        ZFSet.pair value (natCode k.1) ∈ graph ∧
          ∀ other : ZFSet.{u},
            ZFSet.pair other (natCode k.1) ∈ graph → other = value := by
      intro k
      exact hfunctional (natCode k.1)
        ((mem_natCode_iff_exists_lt _ n).mpr ⟨k.1, k.2, rfl⟩)
    let valueAt : Fin n → ZFSet.{u} := fun k => Classical.choose (hvalue k)
    let xs : List ZFSet.{u} := List.ofFn valueAt
    refine ⟨xs, graph, ?_, ?_⟩
    · simpa only [xs, List.length_ofFn] using hsequence
    · intro k
      let kn : Fin n := ⟨k.1, by simpa only [xs, List.length_ofFn] using k.2⟩
      have hk := Classical.choose_spec (hvalue kn)
      simpa only [xs, List.get_ofFn, kn] using hk
  · rintro ⟨xs, graph, hsequence, hgraph⟩
    refine ⟨natCode xs.length, graph, hsequence, ?_, ?_⟩
    · exact (mem_omega_iff_exists_natCode _).mpr ⟨xs.length, rfl⟩
    · intro index hindex
      rcases (mem_natCode_iff_exists_lt index xs.length).mp hindex with
        ⟨k, hk, rfl⟩
      let i : Fin xs.length := ⟨k, hk⟩
      refine ⟨xs.get i, (hgraph i).1, ?_⟩
      exact (hgraph i).2



end Constructible.IndexedSequenceZF
end CUAdapterModule35



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTrace -/
section CUAdapterModule36
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Finite execution traces for rudimentary stack programs

The object-language evaluator quantifies over a set-coded finite trace. This
file isolates the corresponding external machine theorem: successful
evaluation is equivalent to a finite chain of local `runStackToken` steps.
It also records constructibility of every state and of the indexed trace code.
-/


universe u v

namespace Constructible.Godel.RudimentaryTerm

/-! ## Recursive traces and their endpoint semantics -/

/--
A trace contains the input state, every intermediate state, and the final
state.  Consequently a trace for `program` has `program.length + 1` entries.
-/
inductive ExecutionTrace {A : Type u} (rho : A → ZFSet.{v}) :
    List (StackToken A) → List (List ZFSet.{v}) → Prop
  | nil (stack : List ZFSet.{v}) : ExecutionTrace rho [] [stack]
  | cons {token : StackToken A} {program : List (StackToken A)}
      {input next : List ZFSet.{v}} {states : List (List ZFSet.{v})}
      (step : runStackToken rho token input = some next)
      (tail : ExecutionTrace rho program (next :: states)) :
      ExecutionTrace rho (token :: program) (input :: next :: states)

theorem ExecutionTrace.length {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program states) :
    states.length = program.length + 1 := by
  induction htrace with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem ExecutionTrace.nonempty {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program states) : states ≠ [] := by
  intro hnil
  have hlength := htrace.length
  simp only [hnil, List.length_nil] at hlength
  omega

/-- A trace determines the ordinary recursive evaluator and its last state. -/
theorem ExecutionTrace.run_eq_getLast {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {input : List ZFSet.{v}}
    {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program (input :: states)) :
    runStackProgram rho program input =
      some ((input :: states).getLast htrace.nonempty) := by
  induction program generalizing input states with
  | nil =>
      cases htrace with
      | nil => rfl
  | cons token program ih =>
      cases htrace with
      | cons hstep htail =>
          rw [runStackProgram, hstep]
          simp only [Option.bind_some]
          rw [ih htail]
          congr 1

/-- Every successful run has its canonical finite chain of local steps. -/
theorem exists_executionTrace_of_run {A : Type u} (rho : A → ZFSet.{v})
    (program : List (StackToken A)) (input output : List ZFSet.{v})
    (hrun : runStackProgram rho program input = some output) :
    ∃ states : List (List ZFSet.{v}),
      ExecutionTrace rho program states ∧
        states.head? = some input ∧ states.getLast? = some output := by
  induction program generalizing input with
  | nil =>
      simp only [runStackProgram_nil, Option.some.injEq] at hrun
      subst output
      exact ⟨[input], .nil input, rfl, rfl⟩
  | cons token program ih =>
      simp only [runStackProgram] at hrun
      cases hstep : runStackToken rho token input with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep, Option.bind_some] at hrun
          rcases ih next hrun with ⟨tail, htail, hhead, hlast⟩
          cases tail with
          | nil => simp at hhead
          | cons first rest =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst first
              refine ⟨input :: next :: rest, .cons hstep htail, rfl, ?_⟩
              simpa only [List.getLast?_cons_cons] using hlast

/-- A trace with specified endpoints yields the ordinary successful run. -/
theorem run_of_executionTrace {A : Type u} (rho : A → ZFSet.{v})
    (program : List (StackToken A)) (states : List (List ZFSet.{v}))
    (input output : List ZFSet.{v})
    (htrace : ExecutionTrace rho program states)
    (hhead : states.head? = some input)
    (hlast : states.getLast? = some output) :
    runStackProgram rho program input = some output := by
  cases states with
  | nil => exact False.elim (htrace.nonempty rfl)
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      rw [htrace.run_eq_getLast]
      have hne : input :: rest ≠ [] := List.cons_ne_nil input rest
      rw [List.getLast?_eq_some_getLast hne] at hlast
      exact hlast



/-! ## Indexed characterization -/

/--
The form directly mirrored by an object-language trace formula: the state
sequence has one more entry than the program, and instruction `k` takes state
`k` to state `k+1`.
-/
def IndexedExecutionTrace {A : Type u} (rho : A → ZFSet.{v})
    (program : List (StackToken A)) (states : List (List ZFSet.{v})) : Prop :=
  ∃ hlength : states.length = program.length + 1,
    ∀ k : Fin program.length,
      runStackToken rho (program.get k)
          (states.get ⟨k.1, by omega⟩) =
        some (states.get ⟨k.1 + 1, by omega⟩)

/-- Recursive traces satisfy the indexed local-step characterization. -/
theorem ExecutionTrace.indexed {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program states) :
    IndexedExecutionTrace rho program states := by
  induction htrace with
  | nil stack =>
      refine ⟨rfl, ?_⟩
      intro k
      exact Fin.elim0 k
  | @cons token program input next tailStates hstep htail ih =>
      rcases ih with ⟨hlength, hsteps⟩
      refine ⟨by simp only [List.length_cons, hlength], ?_⟩
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa using hstep
      · simpa using hsteps j





/-! ## Constructibility of successful traces -/

/-- One successful local step preserves constructibility of stack entries. -/
theorem runStackToken_entries_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (hstep : runStackToken (rudimentaryGenerator U) token input = some output) :
    ∀ x ∈ output, x ∈ L := by
  cases token with
  | inl generator =>
      simp only [runStackToken, Option.some.injEq] at hstep
      subst output
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact rudimentaryGenerator_mem_L hU generator
      · exact hinput x hx
  | inr operation =>
      cases input with
      | nil => simp [runStackToken] at hstep
      | cons right tail =>
          cases tail with
          | nil => simp [runStackToken] at hstep
          | cons left rest =>
              simp only [runStackToken, Option.some.injEq] at hstep
              subst output
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact op_mem_L (i := operation)
                  (hinput left (by simp)) (hinput right (by simp))
              · exact hinput x (by simp [hx])

/-- Every state occurring in a successful constructible-seed trace is finite
and consists entirely of constructible sets. -/
theorem ExecutionTrace.entries_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    {program : List (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    {input : List ZFSet.{u}} (hhead : states.head? = some input)
    (hinput : ∀ x ∈ input, x ∈ L) :
    ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L := by
  induction htrace generalizing input with
  | nil stack =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      simpa using hinput
  | @cons token program input next tailStates hstep htail ih =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      have hnext : ∀ x ∈ next, x ∈ L :=
        runStackToken_entries_mem_L hU token _ _ hinput hstep
      intro stack hstack
      simp only [List.mem_cons] at hstack
      rcases hstack with rfl | hstack
      · exact hinput
      · exact ih rfl hnext stack
          (by simpa only [List.mem_cons] using hstack)





end Constructible.Godel.RudimentaryTerm
end CUAdapterModule36


