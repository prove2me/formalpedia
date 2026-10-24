-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library10
-- name    : CH_ConstructibleAC_Library10
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:23:13.028427+00:00
-- url     : https://prove2.me/theorems/ef7695c0-7350-4ee8-abb1-18ab719c0078
-- title:
--   Absolute execution and coded stage histories
-- statement:
--   A coded stage history records the well-ordering data assigned to earlier constructible stages. This library supplies the absolute-evaluation interfaces, the parameters and base formula for such histories, and the definable relation graphs and entry interfaces used to decode them. These definitions prepare the recursive construction of histories whose entries are themselves constructible sets.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgramEvalAbsolute.lean#L1-L1272; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryParameters.lean#L1-L122; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryBaseFormula.lean#L1-L51; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/DefinableRelationGraph.lean#L1-L259; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryEntry.lean#L1-L158

import Definitions.Def_CH_ConstructibleAC_Library09
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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalAbsolute -/
section CUAdapterModule62
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of the fixed postfix-program evaluator

The ambient evaluator accepts arbitrary finite indexed codes.  For the
constructible universe we need more: every unbounded witness used by an
evaluation certificate must itself belong to `L`.  This file proves the
restricted semantics for genuine program codes by projecting restricted
certificates to the ambient universe and, conversely, by encoding the
canonical execution trace of a successful run.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF
open Constructible.FiniteSequenceZF

local notation "LMem" => Model.lCarrierMem



@[simp]
 theorem subtypeVal_snoc_apply {n : Nat}
    (s : Tuple Model.LCarrier.{u} n) (x : Model.LCarrier.{u})
    (i : Fin (n + 1)) :
    (snoc s x i).1 = snoc (fun j => (s j).1) x.1 i := by
  exact congrFun (Model.subtypeVal_snoc s x) i

/-! ## One-way projection to the ambient universe -/

/-- Restricted validity of a constructible sequence implies ambient validity. -/
 theorem sequenceValidity_lCarrier_to_ambient
    (omega sequence : Model.LCarrier.{u})
    (hvalid :
      FOFormula.Satisfies LMem sequenceValidityFormula ![omega, sequence]) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      ![omega.1, sequence.1] := by
  rw [satisfies_sequenceValidityFormula_lCarrier] at hvalid
  rw [IndexedSequenceZF.satisfies_sequenceValidityFormula]
  rcases hvalid with
    ⟨length, graph, hsequence, hlength, hfunctional⟩
  refine ⟨length.1, graph.1, hsequence, hlength, ?_⟩
  intro index hindex
  let indexL : Model.LCarrier.{u} :=
    ⟨index, mem_L_of_mem hindex length.2⟩
  rcases hfunctional indexL hindex with
    ⟨value, hvalue, hunique⟩
  refine ⟨value.1, hvalue, ?_⟩
  intro other hother
  let otherL : Model.LCarrier.{u} :=
    ⟨other,
      mem_L_of_mem (pair_left_mem_pairField hother)
        (pairField_mem_L graph.2)⟩
  exact hunique otherL hother

 theorem sequenceValidityAssignment_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 2)
    (hvalid : FOFormula.Satisfies LMem sequenceValidityFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      (fun i => (s i).1) := by
  have hstandard :
      FOFormula.Satisfies LMem sequenceValidityFormula ![s 0, s 1] := by
    apply (satisfies_congr_assignment LMem sequenceValidityFormula
      s ![s 0, s 1] ?_).mp hvalid
    intro i
    fin_cases i <;> rfl
  have hambient := sequenceValidity_lCarrier_to_ambient
    (s 0) (s 1) hstandard
  apply (satisfies_congr_assignment Delta0Formula.ZFMem
    sequenceValidityFormula ![(s 0).1, (s 1).1]
      (fun i => (s i).1) ?_).mp hambient
  intro i
  fin_cases i <;> rfl

/-- The sole graph witness of `hasLengthFormula` also projects to the ambient universe. -/
 theorem hasLength_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 2)
    (hlength : FOFormula.Satisfies LMem hasLengthFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
      (fun i => (s i).1) := by
  simp only [hasLengthFormula, FOFormula.Satisfies] at hlength ⊢
  rcases hlength with ⟨graph, hgraph⟩
  refine ⟨graph.1, ?_⟩
  have hraw :=
    (Delta0Formula.satisfies_toFO_lCarrier_absolute _
      (snoc s graph)).mp hgraph
  simpa only [Model.subtypeVal_snoc] using hraw

/-- The variable branch has no new ambient witnesses beyond its `L` witness. -/
 theorem variableStackStep_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem variableStackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem variableStackStepFormula
      (fun i => (s i).1) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with ⟨generator, htoken, hgenerator, houtput⟩
  refine ⟨generator.1, ?_, ?_, ?_⟩
  · have htokenRaw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc s generator)).mp htoken
    simpa only [Model.subtypeVal_snoc] using htokenRaw
  · rcases hgenerator with hgenerator | hgenerator
    · exact Or.inl (congrArg Subtype.val hgenerator)
    · exact Or.inr hgenerator
  · have houtputRaw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc s generator)).mp houtput
    simpa only [Model.subtypeVal_snoc] using houtputRaw

/-- Each operation branch likewise projects all of its constructible witnesses. -/
 theorem operationStackStep_lCarrier_to_ambient (i : Fin 9)
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem (operationStackStepFormula i) s) :
    FOFormula.Satisfies Delta0Formula.ZFMem (operationStackStepFormula i)
      (fun j => (s j).1) := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨right, left, rest, result, inner,
      htoken, hinput, hinner, houtput, hop⟩
  refine ⟨right.1, left.1, rest.1, result.1, inner.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp htoken
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp hinput
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp hinner
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp houtput
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hop
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      (opGraphFormula i).toFO _ _ ?_).mp hraw
    intro j
    simp only [subtypeVal_snoc_apply]

/-- A restricted raw stack step is always an ambient raw stack step. -/
 theorem stackStep_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem stackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
      (fun i => (s i).1) := by
  simp only [stackStepFormula, anyOperationStackStepFormula,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with hvariable | hoperation
  · exact Or.inl (variableStackStep_lCarrier_to_ambient s hvariable)
  · right
    rcases hoperation with h | h | h | h | h | h | h | h | h
    · exact Or.inl (operationStackStep_lCarrier_to_ambient 0 s h)
    · exact Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 1 s h))
    · exact Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 2 s h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 3 s h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 4 s h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 5 s h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (operationStackStep_lCarrier_to_ambient 6 s h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl
          (operationStackStep_lCarrier_to_ambient 7 s h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr
          (operationStackStep_lCarrier_to_ambient 8 s h))))))))

/-- A restricted local trace transition projects to the ambient transition. -/
 theorem traceStep_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem traceStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
      (fun i => (s i).1) := by
  simp only [traceStepFormula, traceStepBody, FOFormula.Satisfies,
    FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstack⟩
  refine ⟨token.1, input.1, succ.1, output.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp htoken
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hinput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hsucc
    change FOFormula.Satisfies Delta0Formula.ZFMem
      (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20)) _ at hraw
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp houtput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]
  · have hraw := stackStep_lCarrier_to_ambient _ hstack
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackStepFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]

/-- The evaluator core projects one conjunct at a time, avoiding large tuple reduction. -/
 theorem stackProgramEvalCore_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 20)
    (hcore : FOFormula.Satisfies LMem stackProgramEvalCore s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalCore
      (fun i => (s i).1) := by
  rw [stackProgramEvalCore] at hcore ⊢
  rcases hcore with
    ⟨hprogramLength, htraceLength, hsuccessor,
      hinitial, hfinal, hfinalStack, hsteps⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramLength ⊢
    exact hasLength_lCarrier_to_ambient _ hprogramLength
  · rw [FOFormula.satisfies_rename] at htraceLength ⊢
    exact hasLength_lCarrier_to_ambient _ htraceLength
  · exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ s).mp hsuccessor
  · rw [FOFormula.satisfies_rename] at hinitial ⊢
    exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hinitial
  · rw [FOFormula.satisfies_rename] at hfinal ⊢
    exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hfinal
  · exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ s).mp hfinalStack
  · rw [FOFormula.satisfies_boundedAll] at hsteps ⊢
    intro index hindex
    let indexL : Model.LCarrier.{u} :=
      ⟨index, mem_L_of_mem hindex (s 17).2⟩
    have hrestricted := hsteps indexL hindex
    rw [FOFormula.satisfies_rename] at hrestricted ⊢
    have hambient := traceStep_lCarrier_to_ambient _ hrestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      traceStepFormula _ _ ?_).mp hambient
    intro i
    simp only [subtypeVal_snoc_apply, indexL]

/-- Every restricted evaluator certificate is also an ambient certificate. -/
 theorem stackProgramEval_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
      (fun i => (s i).1) := by
  rw [stackProgramEvalFormula] at heval ⊢
  rcases heval with
    ⟨hprogramValid, trace, htraceValid,
      programLength, traceLength, finalStack, hcore⟩
  refine ⟨?_, trace.1, ?_, programLength.1, traceLength.1,
    finalStack.1, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramValid ⊢
    exact sequenceValidityAssignment_lCarrier_to_ambient _ hprogramValid
  · rw [FOFormula.satisfies_rename] at htraceValid ⊢
    let traceValidityAssignment : Tuple Model.LCarrier.{u} 2 :=
      fun i => snoc s trace (evalTraceValidityRename i)
    have htraceRestricted :
        FOFormula.Satisfies LMem sequenceValidityFormula
          traceValidityAssignment := by
      exact htraceValid
    have htraceAmbient :=
      sequenceValidityAssignment_lCarrier_to_ambient
        traceValidityAssignment htraceRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      sequenceValidityFormula _ _ ?_).mp htraceAmbient
    intro i
    simp only [traceValidityAssignment, subtypeVal_snoc_apply]
  · let coreAssignment : Tuple Model.LCarrier.{u} 20 :=
      snoc (snoc (snoc (snoc s trace) programLength)
        traceLength) finalStack
    have hcoreRestricted :
        FOFormula.Satisfies LMem stackProgramEvalCore coreAssignment := by
      exact hcore
    have hambient := stackProgramEvalCore_lCarrier_to_ambient
      coreAssignment hcoreRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackProgramEvalCore _ _ ?_).mp hambient
    intro i
    simp only [coreAssignment, subtypeVal_snoc_apply]

/-! ## Genuine evaluator assignments -/

/-- The thirteen fixed stack-machine parameters, all packaged in `L`. -/
def stackStepPrefixLAssignment (U : ZFSet.{u}) (hU : U ∈ L) :
    Tuple Model.LCarrier.{u} 13 :=
  ![⟨U, hU⟩,
    ⟨varTag, varTag_mem_L⟩,
    ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨operationCode 0, operationCode_mem_L 0⟩,
    ⟨operationCode 1, operationCode_mem_L 1⟩,
    ⟨operationCode 2, operationCode_mem_L 2⟩,
    ⟨operationCode 3, operationCode_mem_L 3⟩,
    ⟨operationCode 4, operationCode_mem_L 4⟩,
    ⟨operationCode 5, operationCode_mem_L 5⟩,
    ⟨operationCode 6, operationCode_mem_L 6⟩,
    ⟨operationCode 7, operationCode_mem_L 7⟩,
    ⟨operationCode 8, operationCode_mem_L 8⟩]

theorem stackStepPrefixLAssignment_val (U : ZFSet.{u}) (hU : U ∈ L) :
    (fun i => (stackStepPrefixLAssignment U hU i).1) =
      stackStepPrefixAssignment U := by
  funext i
  fin_cases i <;> rfl

/-- The evaluator assignment for an arbitrary constructible program code. -/
def stackProgramEvalCodeLAssignment
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L) :
    Tuple Model.LCarrier.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixLAssignment U hU)
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
    ⟨code, hcode⟩) ⟨result, hresult⟩

theorem stackProgramEvalCodeLAssignment_val
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L) :
    (fun i =>
      (stackProgramEvalCodeLAssignment U code result
        hU hcode hresult i).1) =
      stackProgramEvalAssignment U code result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalCodeLAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixLAssignment_val U hU) i12

/-- Restricted satisfaction for an arbitrary constructible code projects to
the ambient evaluator semantics. -/
theorem satisfies_stackProgramEvalFormula_code_lCarrier_to_ambient
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalCodeLAssignment U code result
        hU hcode hresult)) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
      (stackProgramEvalAssignment U code result) := by
  have hambient := stackProgramEval_lCarrier_to_ambient _ heval
  simpa only [stackProgramEvalCodeLAssignment_val] using hambient

/-- Every arbitrary constructible evaluator witness decodes to a genuine
postfix program with the stated result. -/
theorem satisfies_stackProgramEvalFormula_code_lCarrier_to_exists_run
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalCodeLAssignment U code result
        hU hcode hresult)) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      Represents code (encodedStackProgram U program) ∧
        runStackProgram (rudimentaryGenerator U) program [] =
          some [result] := by
  apply (satisfies_stackProgramEvalFormula_iff_exists_run
    U code result).mp
  exact satisfies_stackProgramEvalFormula_code_lCarrier_to_ambient
    U code result hU hcode hresult heval

/-- The genuine evaluator assignment, with every free coordinate in `L`. -/
def stackProgramEvalLAssignment (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    Tuple Model.LCarrier.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixLAssignment U hU)
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩)
    ⟨result, hresult⟩

theorem stackProgramEvalLAssignment_val (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    (fun i =>
      (stackProgramEvalLAssignment U hU program result hresult i).1) =
      stackProgramEvalAssignment U (stackProgramZFCode U program) result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalLAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixLAssignment_val U hU) i12

 theorem stackProgramEvalLAssignment_empty
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    stackProgramEvalLAssignment U hU program result hresult (3 : Fin 16) =
      (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}) := by
  apply Subtype.ext
  have hval := congrFun
    (stackProgramEvalLAssignment_val U hU program result hresult)
    (3 : Fin 16)
  simpa only [stackProgramEvalAssignment_empty] using hval

/-- Soundness of restricted evaluation on a genuine program code. -/
theorem satisfies_stackProgramEvalFormula_lCarrier_to_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalLAssignment U hU program result hresult)) :
    runStackProgram (rudimentaryGenerator U) program [] =
      some [result] := by
  apply (satisfies_stackProgramEvalFormula_iff_run U program result).mp
  have hambient := stackProgramEval_lCarrier_to_ambient _ heval
  simpa only [stackProgramEvalLAssignment_val] using hambient

/-! ## Constructible canonical traces -/

 theorem encodedStackStates_entries_mem_L
    {states : List (List ZFSet.{u})}
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L) :
    ∀ code ∈ encodedStackStates states, code ∈ L := by
  intro code hcode
  rcases List.mem_map.mp hcode with ⟨stack, hstack, rfl⟩
  exact listCode_mem_L (hstates stack hstack)

 def traceStepExecutionLAssignment
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) : Tuple Model.LCarrier.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixLAssignment U hU)
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩)
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩)
    ⟨natCode k, natCode_mem_L k⟩

 theorem traceStepExecutionLAssignment_val
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) :
    (fun i =>
      (traceStepExecutionLAssignment U hU program states
        hstateCodes k i).1) =
      traceStepAssignment U (stackProgramZFCode U program)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states))
        (natCode k) := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [traceStepExecutionLAssignment, traceStepAssignment,
          stackStepAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixLAssignment_val U hU) i12

 theorem comp_traceStepProgramValueRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) (token input succ output : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k) token) input) succ) output
        (traceStepProgramValueRename i)) =
      ![⟨stackProgramZFCode U program,
          stackProgramZFCode_mem_L hU program⟩,
        ⟨natCode k, natCode_mem_L k⟩, token] := by
  funext i
  fin_cases i <;> rfl

 theorem comp_traceStepInputValueRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) (token input succ output : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k) token) input) succ) output
        (traceStepInputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        ⟨natCode k, natCode_mem_L k⟩, input] := by
  funext i
  fin_cases i <;> rfl

 theorem comp_traceStepOutputValueRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) (token input succ output : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k) token) input) succ) output
        (traceStepOutputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        succ, output] := by
  funext i
  fin_cases i <;> rfl

 theorem comp_traceStepStackStepRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L)
    (succ : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k)
        ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩)
        ⟨listCode input, listCode_mem_L hinput⟩) succ)
        ⟨listCode output, listCode_mem_L houtput⟩
        (traceStepStackStepRename i)) =
      stackStepLAssignment U hU token input output hinput houtput := by
  funext i
  apply Subtype.ext
  have hextendedVal :
      (fun j =>
        (snoc (snoc (snoc (snoc
          (traceStepExecutionLAssignment U hU program states
            hstateCodes k)
          ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩)
          ⟨listCode input, listCode_mem_L hinput⟩) succ)
          ⟨listCode output, listCode_mem_L houtput⟩ j).1) =
        snoc (snoc (snoc (snoc
          (traceStepAssignment U (stackProgramZFCode U program)
            (IndexedSequenceZF.sequenceCode (encodedStackStates states))
            (natCode k))
          (stackTokenZFCode U token)) (listCode input)) succ.1)
          (listCode output) := by
    rw [Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      traceStepExecutionLAssignment_val]
  have hraw := congrFun
    (comp_traceStepStackStepRename U (stackProgramZFCode U program)
      (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode k) (stackTokenZFCode U token) (listCode input)
      succ.1 (listCode output)) i
  rw [congrFun hextendedVal (traceStepStackStepRename i),
    congrFun (stackStepLAssignment_val U hU token input output
      hinput houtput) i]
  exact hraw

/-- Every genuine indexed execution step has an entirely constructible certificate. -/
 theorem satisfies_traceStepFormula_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L)
    (k : Nat) (hk : k < program.length) :
    FOFormula.Satisfies LMem traceStepFormula
      (traceStepExecutionLAssignment U hU program states
        (encodedStackStates_entries_mem_L hstates) k) := by
  have hlength := htrace.length
  have hi : k < states.length := by omega
  have ho : k + 1 < states.length := by omega
  let token := program.get ⟨k, hk⟩
  let input := states.get ⟨k, hi⟩
  let output := states.get ⟨k + 1, ho⟩
  have hinput : ∀ x ∈ input, x ∈ L :=
    hstates input (List.get_mem states ⟨k, hi⟩)
  have houtput : ∀ x ∈ output, x ∈ L :=
    hstates output (List.get_mem states ⟨k + 1, ho⟩)
  let tokenL : Model.LCarrier.{u} :=
    ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩
  let inputL : Model.LCarrier.{u} :=
    ⟨listCode input, listCode_mem_L hinput⟩
  let succL : Model.LCarrier.{u} :=
    ⟨natCode (k + 1), natCode_mem_L (k + 1)⟩
  let outputL : Model.LCarrier.{u} :=
    ⟨listCode output, listCode_mem_L houtput⟩
  rw [traceStepFormula]
  refine ⟨tokenL, inputL, succL, outputL, ?_⟩
  rw [traceStepBody]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename,
      comp_traceStepProgramValueRename_execution]
    apply (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackProgram U program)
      (stackTokenCodes_mem_L hU program) k tokenL).mpr
    refine ⟨by simpa only [encodedStackProgram, List.length_map] using hk, ?_⟩
    simp only [encodedStackProgram, tokenL, token,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepInputValueRename_execution]
    apply (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackStates states)
      (encodedStackStates_entries_mem_L hstates) k inputL).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using hi, ?_⟩
    simp only [encodedStackStates, inputL, input,
      List.get_eq_getElem, List.getElem_map]
  · apply (Delta0Formula.satisfies_successorFOAt_lCarrier
      (18 : Fin 20) (15 : Fin 20) _).mpr
    exact natCode_succ_eq_insert k
  · rw [FOFormula.satisfies_rename,
      comp_traceStepOutputValueRename_execution]
    apply (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackStates states)
      (encodedStackStates_entries_mem_L hstates) (k + 1) outputL).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using ho, ?_⟩
    simp only [encodedStackStates, outputL, output,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepStackStepRename_execution
        (hinput := hinput) (houtput := houtput)]
    apply (satisfies_stackStepFormula_lCarrier_iff_run
      U hU token input output hinput houtput).mpr
    rcases htrace.indexed with ⟨_hlength, hsteps⟩
    simpa only [token, input, output] using hsteps ⟨k, hk⟩

 def stackProgramEvalCoreExecutionLAssignment
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    Tuple Model.LCarrier.{u} 20 :=
  snoc (snoc (snoc (snoc
    (stackProgramEvalLAssignment U hU program result hresult)
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩)
    ⟨natCode program.length, natCode_mem_L program.length⟩)
    ⟨natCode states.length, natCode_mem_L states.length⟩)
    ⟨listCode [result], listCode_mem_L (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hresult)⟩

 theorem stackProgramEvalCoreExecutionLAssignment_val
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (fun i =>
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes i).1) =
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U (stackProgramZFCode U program) result)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
        (natCode program.length)) (natCode states.length))
        (listCode [result]) := by
  rw [stackProgramEvalCoreExecutionLAssignment,
    Model.subtypeVal_snoc, Model.subtypeVal_snoc,
    Model.subtypeVal_snoc, Model.subtypeVal_snoc,
    stackProgramEvalLAssignment_val]

 theorem stackProgramEvalCoreExecutionLAssignment_trace
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (16 : Fin 20) =
      ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
        IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩ := by
  change stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes
      (Fin.last 16).castSucc.castSucc.castSucc = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_castSucc, snoc_last]

 theorem stackProgramEvalCoreExecutionLAssignment_programLength
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (17 : Fin 20) =
      ⟨natCode program.length, natCode_mem_L program.length⟩ := by
  change stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes (Fin.last 17).castSucc.castSucc = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_last]

 theorem stackProgramEvalCoreExecutionLAssignment_finalStack
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (19 : Fin 20)).1 = listCode [result] := by
  change (stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes (Fin.last 19)).1 = _
  rw [stackProgramEvalCoreExecutionLAssignment, snoc_last]

 theorem stackProgramEvalCoreExecutionLAssignment_result
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (15 : Fin 20)).1 = result := by
  change (stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes
      (Fin.last 15).castSucc.castSucc.castSucc.castSucc).1 = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_castSucc, snoc_castSucc,
    stackProgramEvalLAssignment, snoc_last]

 theorem stackProgramEvalCoreExecutionLAssignment_empty
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (3 : Fin 20) =
      (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}) := by
  change stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes
      (3 : Fin 16).castSucc.castSucc.castSucc.castSucc = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_castSucc, snoc_castSucc]
  exact stackProgramEvalLAssignment_empty U hU program result hresult

/-- The bounded local-step conjunct of a genuine execution trace. -/
 theorem satisfies_evalTraceSteps_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L)
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (FOFormula.boundedAll (17 : Fin 20)
        (FOFormula.rename evalTraceStepRename traceStepFormula))
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  rw [FOFormula.satisfies_boundedAll]
  intro index hindex
  change index.1 ∈ natCode program.length at hindex
  rcases (mem_natCode_iff index.1 program.length).mp hindex with
    ⟨k, hk, hindexValue⟩
  have hindex : index =
      (⟨natCode k, natCode_mem_L k⟩ : Model.LCarrier.{u}) :=
    Subtype.ext hindexValue
  subst index
  rw [FOFormula.satisfies_rename]
  have hlocal := satisfies_traceStepFormula_execution_lCarrier
    U hU program states htrace hstates k hk
  apply (satisfies_congr_assignment LMem traceStepFormula _ _ ?_).mpr
    hlocal
  intro i
  apply Subtype.ext
  have hextendedVal :
      (fun j =>
        (snoc (stackProgramEvalCoreExecutionLAssignment U hU program
            result hresult states hstateCodes)
          (⟨natCode k, natCode_mem_L k⟩ : Model.LCarrier.{u}) j).1) =
        snoc (snoc (snoc (snoc (snoc
          (stackProgramEvalAssignment U (stackProgramZFCode U program)
            result)
          (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
          (natCode program.length)) (natCode states.length))
          (listCode [result])) (natCode k) := by
    rw [Model.subtypeVal_snoc,
      stackProgramEvalCoreExecutionLAssignment_val]
  have hraw := congrFun
    (comp_evalTraceStepRename U (stackProgramZFCode U program)
      result (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode program.length) (natCode states.length)
      (listCode [result]) (natCode k)) i
  rw [congrFun hextendedVal (evalTraceStepRename i),
    congrFun (traceStepExecutionLAssignment_val U hU program states
      hstateCodes k) i]
  exact hraw

 theorem satisfies_evalProgramLength_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalProgramLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  have hprogramCodes :
      ∀ code ∈ encodedStackProgram U program, code ∈ L := by
    simpa only [encodedStackProgram] using stackTokenCodes_mem_L hU program
  let programL : Model.LCarrier.{u} :=
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩
  let programLengthL : Model.LCarrier.{u} :=
    ⟨natCode program.length, natCode_mem_L program.length⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i =>
        stackProgramEvalCoreExecutionLAssignment U hU program result
          hresult states hstateCodes (evalProgramLengthRename i)) =
        ![programL, programLengthL] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_lCarrier_iff
    (encodedStackProgram U program) hprogramCodes programLengthL).mpr
  simp only [programLengthL, encodedStackProgram, List.length_map]

 theorem satisfies_evalTraceLength_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  let traceL : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩
  let traceLengthL : Model.LCarrier.{u} :=
    ⟨natCode states.length, natCode_mem_L states.length⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i =>
        stackProgramEvalCoreExecutionLAssignment U hU program result
          hresult states hstateCodes (evalTraceLengthRename i)) =
        ![traceL, traceLengthL] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_lCarrier_iff
    (encodedStackStates states) hstateCodes traceLengthL).mpr
  simp only [traceLengthL, encodedStackStates, List.length_map]

 theorem satisfies_evalSuccessor_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hlength : states.length = program.length + 1) :
    FOFormula.Satisfies LMem
      (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  apply (Delta0Formula.satisfies_successorFOAt_lCarrier
    (18 : Fin 20) (17 : Fin 20) _).mpr
  change natCode states.length =
    insert (natCode program.length) (natCode program.length)
  rw [hlength]
  exact natCode_succ_eq_insert program.length

 theorem exists_encodedStackStates_zero_eq
    (states : List (List ZFSet.{u}))
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    ∃ hzero : 0 < (encodedStackStates states).length,
      listCode [] = (encodedStackStates states).get ⟨0, hzero⟩ := by
  have hrawHead :
      (encodedStackStates states).head? = some (listCode []) := by
    simp only [encodedStackStates, List.head?_map, hhead,
      Option.map_some]
  have hzero : 0 < (encodedStackStates states).length := by
    simpa only [encodedStackStates, List.length_map] using hstatesNonempty
  refine ⟨hzero, ?_⟩
  rw [List.head?_eq_getElem?,
    List.getElem?_eq_getElem hzero] at hrawHead
  exact (Option.some.inj hrawHead).symm

 theorem comp_evalInitialValueRename_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (fun i =>
      stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes (evalInitialValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}),
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u})] := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun x => ?_) j) i
  · exact stackProgramEvalCoreExecutionLAssignment_trace
      U hU program result hresult states hstateCodes
  · exact stackProgramEvalCoreExecutionLAssignment_empty
      U hU program result hresult states hstateCodes
  · fin_cases x
    exact stackProgramEvalCoreExecutionLAssignment_empty
      U hU program result hresult states hstateCodes

 theorem satisfies_valueAt_zero_encodedStackStates_lCarrier
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies LMem valueAtFormula
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}),
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u})] := by
  rcases exists_encodedStackStates_zero_eq states hstatesNonempty hhead with
    ⟨hrawZero, hrawHeadGet⟩
  let emptyL : Model.LCarrier.{u} := ⟨∅, empty_mem_L⟩
  let zeroL : Model.LCarrier.{u} := ⟨natCode 0, natCode_mem_L 0⟩
  have hvalue :
      FOFormula.Satisfies LMem valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
          zeroL, emptyL] := by
    exact (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackStates states) hstateCodes 0 emptyL).mpr
        ⟨hrawZero, hrawHeadGet⟩
  apply (satisfies_congr_assignment LMem valueAtFormula _ _ ?_).mpr hvalue
  intro i
  fin_cases i
  · rfl
  · apply Subtype.ext
    change (∅ : ZFSet.{u}) = natCode 0
    simp [natCode]
  · rfl

 theorem satisfies_evalInitial_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hlength : states.length = program.length + 1)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalInitialValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  have hvalue :
      FOFormula.Satisfies LMem valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
          (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}),
          (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u})] := by
    exact satisfies_valueAt_zero_encodedStackStates_lCarrier
      states hstateCodes (by omega) hhead
  rw [FOFormula.satisfies_rename]
  apply (satisfies_congr_assignment LMem valueAtFormula _ _ ?_).mpr hvalue
  intro i
  exact congrFun
    (comp_evalInitialValueRename_execution_lCarrier U hU program result
      hresult states hstateCodes) i

 theorem satisfies_evalFinal_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hlength : states.length = program.length + 1)
    (hlast : states.getLast? = some [result]) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalFinalValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  have hrawLast :
      (encodedStackStates states).getLast? =
        some (listCode [result]) := by
    simp only [encodedStackStates, List.getLast?_map, hlast,
      Option.map_some]
  have hrawLength :
      (encodedStackStates states).length = program.length + 1 := by
    simpa only [encodedStackStates, List.length_map] using hlength
  have hrawProgramLength :
      program.length < (encodedStackStates states).length := by omega
  have hrawLastGet :
      listCode [result] =
        (encodedStackStates states).get
          ⟨program.length, hrawProgramLength⟩ := by
    have hgetLast :
        (encodedStackStates states).getLast? =
          some ((encodedStackStates states).get
            ⟨program.length, hrawProgramLength⟩) := by
      rw [List.getLast?_eq_getElem?]
      have hindex :
          (encodedStackStates states).length - 1 = program.length := by
        omega
      rw [hindex, List.getElem?_eq_getElem hrawProgramLength]
      rfl
    rw [hgetLast] at hrawLast
    exact (Option.some.inj hrawLast).symm
  let traceL : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩
  let programLengthL : Model.LCarrier.{u} :=
    ⟨natCode program.length, natCode_mem_L program.length⟩
  let finalStackL : Model.LCarrier.{u} :=
    ⟨listCode [result], listCode_mem_L (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hresult)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i =>
        stackProgramEvalCoreExecutionLAssignment U hU program result
          hresult states hstateCodes (evalFinalValueRename i)) =
        ![traceL, programLengthL, finalStackL] := by
    funext i
    fin_cases i
    · exact stackProgramEvalCoreExecutionLAssignment_trace
        U hU program result hresult states hstateCodes
    · exact stackProgramEvalCoreExecutionLAssignment_programLength
        U hU program result hresult states hstateCodes
    · apply Subtype.ext
      exact stackProgramEvalCoreExecutionLAssignment_finalStack
        U hU program result hresult states hstateCodes
  rw [hcomp]
  apply (satisfies_valueAtFormula_lCarrier_iff
    (encodedStackStates states) hstateCodes program.length finalStackL).mpr
  exact ⟨hrawProgramLength, hrawLastGet⟩

 theorem satisfies_evalFinalStack_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (Delta0Formula.kuratowskiPairEqAt
        (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  apply (satisfies_kuratowskiPairEqAt_lCarrier
    (19 : Fin 20) (15 : Fin 20) (3 : Fin 20) _).mpr
  rw [stackProgramEvalCoreExecutionLAssignment_finalStack,
    stackProgramEvalCoreExecutionLAssignment_result]
  have hempty := congrArg Subtype.val
    (stackProgramEvalCoreExecutionLAssignment_empty U hU program result
      hresult states hstateCodes)
  rw [hempty]
  rfl

/-- Length and endpoint checks for the canonical constructible trace. -/
 theorem satisfies_stackProgramEvalCore_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hhead : states.head? = some [])
    (hlast : states.getLast? = some [result])
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L)
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem stackProgramEvalCore
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  rw [stackProgramEvalCore]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact satisfies_evalProgramLength_execution_lCarrier
      U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceLength_execution_lCarrier
      U hU program result hresult states hstateCodes
  · exact satisfies_evalSuccessor_execution_lCarrier
      U hU program result hresult states hstateCodes htrace.length
  · exact satisfies_evalInitial_execution_lCarrier
      U hU program result hresult states hstateCodes htrace.length hhead
  · exact satisfies_evalFinal_execution_lCarrier
      U hU program result hresult states hstateCodes htrace.length hlast
  · exact satisfies_evalFinalStack_execution_lCarrier
      U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceSteps_execution_lCarrier
      U hU program result hresult states htrace hstates hstateCodes

/-- Completeness: a successful run supplies a fully constructible evaluator trace. -/
theorem satisfies_stackProgramEvalFormula_lCarrier_of_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [result]) :
    FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalLAssignment U hU program result hresult) := by
  rcases exists_executionTrace_of_run
      (rudimentaryGenerator U) program [] [result] hrun with
    ⟨states, htrace, hhead, hlast⟩
  have hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L :=
    htrace.entries_mem_L hU hhead (by simp)
  have hstateCodes :
      ∀ code ∈ encodedStackStates states, code ∈ L :=
    encodedStackStates_entries_mem_L hstates
  have hprogramCodes :
      ∀ code ∈ encodedStackProgram U program, code ∈ L := by
    simpa only [encodedStackProgram] using stackTokenCodes_mem_L hU program
  let omegaL : Model.LCarrier.{u} :=
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩
  let programL : Model.LCarrier.{u} :=
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩
  let traceL : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩
  let programLengthL : Model.LCarrier.{u} :=
    ⟨natCode program.length, natCode_mem_L program.length⟩
  let traceLengthL : Model.LCarrier.{u} :=
    ⟨natCode states.length, natCode_mem_L states.length⟩
  let finalStackL : Model.LCarrier.{u} :=
    ⟨listCode [result], listCode_mem_L (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hresult)⟩
  let baseAssignment :=
    stackProgramEvalLAssignment U hU program result hresult
  let traceContext : Tuple Model.LCarrier.{u} 17 :=
    snoc baseAssignment traceL
  rw [stackProgramEvalFormula]
  refine ⟨?_, traceL, ?_, programLengthL, traceLengthL,
    finalStackL, ?_⟩
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => baseAssignment (evalProgramValidityRename i)) =
          ![omegaL, programL] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    simpa only [programL, stackProgramZFCode, encodedStackProgram] using
      (satisfies_sequenceValidity_sequenceCode_lCarrier
        (encodedStackProgram U program) hprogramCodes)
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => traceContext (evalTraceValidityRename i)) =
          ![omegaL, traceL] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact satisfies_sequenceValidity_sequenceCode_lCarrier
      (encodedStackStates states) hstateCodes
  · exact satisfies_stackProgramEvalCore_execution_lCarrier
      U hU program result hresult states htrace hhead hlast
        hstates hstateCodes

/-- Genuine program evaluation is absolute between `LCarrier` and the ambient universe. -/
@[simp]
theorem satisfies_stackProgramEvalFormula_lCarrier_iff_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    FOFormula.Satisfies LMem stackProgramEvalFormula
        (stackProgramEvalLAssignment U hU program result hresult) ↔
      runStackProgram (rudimentaryGenerator U) program [] =
        some [result] := by
  constructor
  · exact satisfies_stackProgramEvalFormula_lCarrier_to_run
      U hU program result hresult
  · exact satisfies_stackProgramEvalFormula_lCarrier_of_run
      U hU program result hresult

end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule62



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryParameters -/
section CUAdapterModule63
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Fixed parameters for constructible-stage histories

All local history rules share thirteen fixed constructible parameters.  The
remaining four coordinates are `(history, index, stage, relation)`.
-/


universe u

namespace Constructible.Model

noncomputable section

/-- The evaluator constants independent of the current stage and relation:
`(varTag, appTag, empty, op0, ..., op8, omega)`. -/
def stageHistoryFixedParameters : Tuple LCarrier.{u} 13 :=
  ![
    ⟨Godel.RudimentaryTerm.varTag,
      Godel.RudimentaryTerm.varTag_mem_L⟩,
    ⟨Godel.RudimentaryTerm.appTag,
      Godel.RudimentaryTerm.appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨Godel.RudimentaryTerm.operationCode 0,
      Godel.RudimentaryTerm.operationCode_mem_L 0⟩,
    ⟨Godel.RudimentaryTerm.operationCode 1,
      Godel.RudimentaryTerm.operationCode_mem_L 1⟩,
    ⟨Godel.RudimentaryTerm.operationCode 2,
      Godel.RudimentaryTerm.operationCode_mem_L 2⟩,
    ⟨Godel.RudimentaryTerm.operationCode 3,
      Godel.RudimentaryTerm.operationCode_mem_L 3⟩,
    ⟨Godel.RudimentaryTerm.operationCode 4,
      Godel.RudimentaryTerm.operationCode_mem_L 4⟩,
    ⟨Godel.RudimentaryTerm.operationCode 5,
      Godel.RudimentaryTerm.operationCode_mem_L 5⟩,
    ⟨Godel.RudimentaryTerm.operationCode 6,
      Godel.RudimentaryTerm.operationCode_mem_L 6⟩,
    ⟨Godel.RudimentaryTerm.operationCode 7,
      Godel.RudimentaryTerm.operationCode_mem_L 7⟩,
    ⟨Godel.RudimentaryTerm.operationCode 8,
      Godel.RudimentaryTerm.operationCode_mem_L 8⟩,
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩]

@[simp]
theorem stageHistoryFixedParameters_empty :
    stageHistoryFixedParameters (2 : Fin 13) = emptyLCarrier :=
  rfl

@[simp]
theorem stageHistoryFixedParameters_last :
    stageHistoryFixedParameters (Fin.last 12) =
      (⟨Ordinal.omega0.toZFSet, omega_mem_L⟩ : LCarrier.{u}) :=
  rfl

/-- Before the final omega coordinate, the fixed history parameters are the
stack-step prefix with its leading universe coordinate removed. -/
theorem stageHistoryFixedParameters_init
    (U : LCarrier.{u}) (i : Fin 12) :
    stageHistoryFixedParameters i.castSucc =
      Godel.RudimentaryTerm.stackStepPrefixLAssignment U.1 U.2 i.succ := by
  fin_cases i <;> rfl

/-- Assignment layout `(fixed13, history, index, stage, relation)`. -/
def stageHistoryStateLAssignment
    (history index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 17 :=
  snoc (snoc (snoc (snoc stageHistoryFixedParameters history) index)
    stage) relation

/-- The empty-set parameter, embedded into the full history-rule layout. -/
def stageHistoryEmptyIndex : Fin 17 :=
  (2 : Fin 13).castSucc.castSucc.castSucc.castSucc

@[simp]
theorem stageHistoryStateLAssignment_emptyParameter
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation
        stageHistoryEmptyIndex =
      emptyLCarrier := by
  simp only [stageHistoryStateLAssignment, stageHistoryEmptyIndex,
    snoc_castSucc, stageHistoryFixedParameters_empty]

@[simp]
theorem stageHistoryStateLAssignment_history
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (13 : Fin 17) =
      history :=
  rfl

@[simp]
theorem stageHistoryStateLAssignment_index
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (14 : Fin 17) =
      index :=
  rfl

@[simp]
theorem stageHistoryStateLAssignment_stage
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (15 : Fin 17) =
      stage :=
  rfl

@[simp]
theorem stageHistoryStateLAssignment_relation
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (16 : Fin 17) =
      relation :=
  rfl

end

end Constructible.Model
end CUAdapterModule63



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryBaseFormula -/
section CUAdapterModule64
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The zero-state clause for constructible-stage histories

In the shared layout `(fixed13, history, index, stage, relation)`, the zero
rule requires all three state coordinates other than the ignored history to
be the empty set.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- The local recursion rule at index zero.  Coordinate `2` among the fixed
parameters is the canonical empty set. -/
def historyBaseStateFormula : FOFormula 17 :=
  .conj
    (.eq (14 : Fin 17) stageHistoryEmptyIndex)
    (.conj
      (.eq (15 : Fin 17) stageHistoryEmptyIndex)
      (.eq (16 : Fin 17) stageHistoryEmptyIndex))

@[simp]
theorem satisfies_historyBaseStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyBaseStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      index = emptyLCarrier ∧
        stage = emptyLCarrier ∧ relation = emptyLCarrier := by
  simp only [historyBaseStateFormula, FOFormula.Satisfies,
    stageHistoryStateLAssignment_index,
    stageHistoryStateLAssignment_stage,
    stageHistoryStateLAssignment_relation,
    stageHistoryStateLAssignment_emptyParameter]

end

end Constructible.Model
end CUAdapterModule64



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.DefinableRelationGraph -/
section CUAdapterModule65
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructible graphs of definable relations

A binary relation given by one fixed first-order formula is not merely an
external Lean predicate.  On a constructible domain, Full Separation produces
an actual Kuratowski-pair graph which belongs to `L`.

The separating set is taken from a sufficiently large constructible stage.
This avoids assuming in advance that the ambient product `d x d` itself is
constructible.
-/


universe u

namespace Constructible

namespace Model

/-- A Kuratowski ordered pair, packaged as an element of `L`. -/
def orderedPairLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  ⟨ZFSet.pair x.1 y.1, orderedPair_mem_L x.2 y.2⟩

@[simp]
theorem orderedPairLCarrier_val (x y : LCarrier.{u}) :
    (orderedPairLCarrier x y).1 = ZFSet.pair x.1 y.1 :=
  rfl

end Model

namespace DefinableRelationGraph

/-!
The input formula has layout `(params, x, y)`.  Under the two witnesses in
`graphFormula`, the larger layout is `(params, domain, pair, x, y)`.
-/

/-- Embed `(params, x, y)` into `(params, domain, pair, x, y)`. -/
def predicateRename {n : Nat} : Fin (n + 2) → Fin (n + 4) :=
  Fin.lastCases
    (Fin.last (n + 3))
    (fun j => Fin.lastCases
      (Fin.castSucc (Fin.last (n + 2)))
      (fun i => i.castSucc.castSucc.castSucc.castSucc)
      j)

theorem comp_predicateRename {A : Type u} {n : Nat}
    (params : Tuple A n) (domain pair x y : A) :
    (fun i => snoc (snoc (snoc (snoc params domain) pair) x) y
      (predicateRename i)) =
      snoc (snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [predicateRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [predicateRename]
    · simp [predicateRename]

/-- The index of `domain` in `(params, domain, pair, x, y)`. -/
def domainIndex (n : Nat) : Fin (n + 4) :=
  (Fin.last n).castSucc.castSucc.castSucc

/-- The index of `pair` in `(params, domain, pair, x, y)`. -/
def pairIndex (n : Nat) : Fin (n + 4) :=
  (Fin.last (n + 1)).castSucc.castSucc

/-- The index of `x` in `(params, domain, pair, x, y)`. -/
def leftIndex (n : Nat) : Fin (n + 4) :=
  (Fin.last (n + 2)).castSucc

/-- The index of `y` in `(params, domain, pair, x, y)`. -/
def rightIndex (n : Nat) : Fin (n + 4) :=
  Fin.last (n + 3)

/--
`graphFormula phi(params, domain, pair)` says that `pair = <x,y>` for
some `x,y ∈ domain` satisfying `phi(params,x,y)`.
-/
def graphFormula {n : Nat} (phi : FOFormula (n + 2)) :
    FOFormula (n + 2) :=
  .ex (.ex
    (.conj
      (.mem (leftIndex n) (domainIndex n))
      (.conj
        (.mem (rightIndex n) (domainIndex n))
        (.conj
          (Delta0Formula.kuratowskiPairEqAt
            (pairIndex n) (leftIndex n) (rightIndex n)).toFO
          (FOFormula.rename predicateRename phi)))))

theorem satisfies_pairEq_lCarrier {n : Nat}
    (pair x y : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
        (Delta0Formula.kuratowskiPairEqAt pair x y).toFO s ↔
      (s pair).1 = ZFSet.pair (s x).1 (s y).1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

theorem satisfies_graphFormula {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple Model.LCarrier.{u} n)
    (domain pair : Model.LCarrier.{u}) :
    FOFormula.Satisfies
        (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
        (graphFormula phi) (snoc (snoc params domain) pair) ↔
      ∃ x y : Model.LCarrier.{u},
        x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
          pair.1 = ZFSet.pair x.1 y.1 ∧
          FOFormula.Satisfies
            (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y) := by
  simp only [graphFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, satisfies_pairEq_lCarrier,
    domainIndex, pairIndex, leftIndex, rightIndex,
    snoc_last, snoc_castSucc, comp_predicateRename]

end DefinableRelationGraph

namespace Model





/-- The relation on a set carrier interpreted by a fixed formula. -/
def formulaRelOn {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u}) :
    InternalCarrier domain → InternalCarrier domain → Prop :=
  fun x y =>
    FOFormula.Satisfies
      (fun z w : LCarrier.{u} => z.1 ∈ w.1)
      phi (snoc (snoc params x.1) y.1)



end Model

end Constructible
end CUAdapterModule65



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryEntry -/
section CUAdapterModule66
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructible codes for stage-history entries

A stage history records triples `(index, stage, relation)`.  This file gives
the constructible triple code and a four-variable first-order lookup formula
whose semantics is exact in `LCarrier`.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- A right-associated Kuratowski triple packaged as an element of `L`. -/
def tripleLCarrier (x y z : LCarrier.{u}) : LCarrier.{u} :=
  orderedPairLCarrier x (orderedPairLCarrier y z)

@[simp]
theorem tripleLCarrier_val (x y z : LCarrier.{u}) :
    (tripleLCarrier x y z).1 = Godel.triple x.1 y.1 z.1 :=
  rfl

/-- Right-associated Kuratowski triples are injective in all coordinates. -/
theorem triple_injective {a b c a' b' c' : ZFSet.{u}}
    (h : Godel.triple a b c = Godel.triple a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  rcases ZFSet.pair_inj.mp h with ⟨ha, htail⟩
  rcases ZFSet.pair_inj.mp htail with ⟨hb, hc⟩
  exact ⟨ha, hb, hc⟩

/-!
The free-variable layout of `historyEntryFormula` is
`(history, index, stage, relation)`.  The existentially bound last variable
is the encoded triple itself.
-/

/-- In an arbitrary context, the selected history contains the triple made
from the other three selected coordinates. -/
def historyEntryAt {n : Nat}
    (history index stage relation : Fin n) : FOFormula n :=
  .ex (.conj
    (.mem (Fin.last n) history.castSucc)
    (Delta0Formula.tripleEqAt
      (Fin.last n) index.castSucc stage.castSucc relation.castSucc).toFO)

/-- A history contains the triple `(index, stage, relation)`. -/
def historyEntryFormula : FOFormula 4 :=
  historyEntryAt (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)

/-- The direct four-coordinate assignment for a history lookup. -/
def historyEntryAssignment
    (history index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 4 :=
  ![history, index, stage, relation]

@[simp]
theorem satisfies_historyEntryAt_components {n : Nat}
    (history index stage relation : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (historyEntryAt history index stage relation) s ↔
      ∃ entry : LCarrier.{u},
        entry.1 ∈ (s history).1 ∧
          entry.1 = Godel.triple
            (s index).1 (s stage).1 (s relation).1 := by
  simp only [historyEntryAt, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _hentry
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt]
  simp only [snoc_last, snoc_castSucc]

/-- Exact arbitrary-context semantics of a history lookup. -/
theorem satisfies_historyEntryAt_iff {n : Nat}
    (history index stage relation : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (historyEntryAt history index stage relation) s ↔
      Godel.triple (s index).1 (s stage).1 (s relation).1 ∈
        (s history).1 := by
  rw [satisfies_historyEntryAt_components]
  constructor
  · rintro ⟨entry, hentry, heq⟩
    simpa only [heq] using hentry
  · intro hentry
    exact
      ⟨tripleLCarrier (s index) (s stage) (s relation),
        by simpa only [tripleLCarrier_val] using hentry,
        tripleLCarrier_val (s index) (s stage) (s relation)⟩

@[simp]
theorem satisfies_historyEntryFormula_components
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyEntryFormula
        (historyEntryAssignment history index stage relation) ↔
      ∃ entry : LCarrier.{u},
        entry.1 ∈ history.1 ∧
          entry.1 = Godel.triple index.1 stage.1 relation.1 := by
  simp only [historyEntryFormula, historyEntryAt, historyEntryAssignment,
    FOFormula.Satisfies, Matrix.cons_val_zero, snoc_last, snoc_castSucc]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _hentry
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt]
  rfl



/-- The external predicate denoted by `historyEntryFormula`. -/
def HistoryEntry
    (history index stage relation : LCarrier.{u}) : Prop :=
  Godel.triple index.1 stage.1 relation.1 ∈ history.1



end

end Constructible.Model
end CUAdapterModule66


