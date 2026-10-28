-- Prove2me | Definitions.Def_OAIQ087A022
-- name    : OAIQ087A022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:33:02.621081+00:00
-- url     : https://prove2.me/theorems/da82cdcc-f11e-44ed-9b63-aadeab66aa7d
-- title:
--   Definitions bundle OAIQ087A022 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 234 declarations of OpenAI's Lean: 71 definitions, 3 inductive types or structures and 160 theorems. The definitions and types are `OAI.MaxCutGames.Explicit.MachineSingleOrbitFinish.finishStartInTime`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitFinish.timePolynomial`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitProgram.machine`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitProgram.program`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRuntime.finalTapes`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRuntime.timePolynomial`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.bodyInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.incrementInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionCompose.certifiedOutput`, `OAI.MaxCutGames.Explicit.MachineSubdivisionCompose.certify`, `OAI.MaxCutGames.Explicit.MachineSubdivisionCorrespondence.Involutive`, `OAI.MaxCutGames.Explicit.MachineSubdivisionEmission.headerInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionEmission.prepareInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionFinish.finishStartInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionFinish.timePolynomial`, `OAI.MaxCutGames.Explicit.MachineSubdivisionHeaders.headersInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionInit.initializeInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionInit.prefixInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionLoop.bodyInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionLoop.loopInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionProgram.machine`, `OAI.MaxCutGames.Explicit.MachineSubdivisionProgram.program`, `OAI.MaxCutGames.Explicit.MachineSubdivisionRuntime.finalTapes`, `OAI.MaxCutGames.Explicit.MachineSubdivisionRuntime.prefixInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionRuntime.timePolynomial`, `OAI.MaxCutGames.Explicit.MachineSubdivisionTableRead.tableInTime`, `OAI.MaxCutGames.Explicit.MachineUniformHeaders.headersInTime`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.machine`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.program`, `OAI.MaxCutGames.Explicit.MachineUniformRun.emitInTime`, `OAI.MaxCutGames.Explicit.MachineUniformRun.finishStartInTime`, `OAI.MaxCutGames.Explicit.MachineUniformRun.prefixInTime`, `OAI.MaxCutGames.Explicit.MachineUniformRun.scaleInTime`, `OAI.MaxCutGames.Explicit.MachineUniformRun.timePolynomial`, `OAI.MaxCutGames.Explicit.ProductPaddedOutput.Embedded.simpleBipartite`, `OAI.MaxCutGames.Explicit.ProductPaddedOutput.side`, `OAI.MaxCutGames.Explicit.SubdivisionTarget.vertexFields`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily.main`, `OAI.MaxCutGames.Integration.AddressTupleBody.Ready`, `OAI.MaxCutGames.Integration.AddressTupleBody.budget` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_SubdivisionEncoding`, `MaxCut_Games_AddressGame`, `MaxCut_Games_AddressOdometerSchedule`, `MaxCut_Games_AddressTupleLoaded`, `MaxCut_Games_CanonicalWordTemplate`, `MaxCut_Games_EquationLookup`, `MaxCut_Games_OccurrenceTupleOrder`, `MaxCut_Games_Product`, `MaxCut_Games_ProductTarget`, `MaxCut_Machines_AddressMachineLoop`, `MaxCut_Machines_AddressMachineProgram`, `MaxCut_Machines_CanonicalBodyMachine`, `MaxCut_Machines_CloneMachineModel`, `MaxCut_Machines_MachineExpanderFamilyCycle`, `MaxCut_Machines_MachineFieldTemplate`, `MaxCut_Machines_MachineRhsLoad`, `MaxCut_Machines_MachineSingleOrbitProgram`, `MaxCut_Machines_MachineSubdivisionCorrespondence`, `MaxCut_Machines_MachineSubdivisionDynamicRows`, `MaxCut_Machines_MachineSubdivisionEmission`, `MaxCut_Machines_MachineSubdivisionTableRead`, `MaxCut_Machines_MachineTemplateAddress`, `MaxCut_Machines_MachineTuple`, `MaxCut_Machines_MachineUnaryAffine`, `MaxCut_Machines_RuntimeSpace`.
--
--   **Imports.** It imports the bundles `OAIQ087A014`, `OAIQ087A015`, `OAIQ087A016` and `OAIQ087A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A029` and `OAIQ087A030`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A014
import Definitions.Def_OAIQ087A015
import Definitions.Def_OAIQ087A016
import Definitions.Def_OAIQ087A017

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFieldTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineFieldTemplate

open Turing
open MaxCutGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q : Nat} {K Λ σ : Type}

variable [DecidableEq K]

def phaseInTime (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label tokens.length → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction tokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (startAt tokens.length 0)), state, base⟩
      (some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩)
      (3 * copiedLength tokens (fun j => base (field j)) + 3 * tokens.length + 1) where
  steps := templateSteps tokens (fun j => base (field j))
  evals_in_steps := phaseTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
    place exit P atInstruction base scratchEmpty state
  steps_le_m := templateSteps_le tokens _

end MaxCutGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUnaryAffine
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real finite program for uniform whole-instance copying. It reads three
headers, physically multiplies the occurrence count by the fixed constant,
copies the header-free body the same fixed number of times, and clears all
working tapes. No input-dependent data are placed in finite control. -/

namespace MaxCutGames.Explicit.MachineUniformProgram

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad

def program (C : Nat) : Label C → TM2.Stmt (fun _ : Tape => Bool) (Label C) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .scale 0 => MachineUnaryAffineAt.seed .newOccurrences 0 (.scale 1)
  | .scale 1 => MachineUnaryAffineAt.scan .occurrences .affineScratch
      .newOccurrences C (.scale 1) (.scale 2)
  | .scale 2 => MachineTransfer.loopAt .affineScratch .occurrences id false
      (.scale 2) (some (emitEntry C))
  | .emit label => MachineFieldTemplate.instruction (tokens C) emitField
      .copyScratch .accumulator Label.emit (some .finishStart) label
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (C : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label C
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program C

end MaxCutGames.Explicit.MachineUniformProgram

/-! Exact execution of the three input-header reads of uniform copying. -/

namespace MaxCutGames.Explicit.MachineUniformHeaders

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineUniformProgram

theorem initList_eq (C : Nat) (bits : List Bool) :
    initList (machine C) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

/-- The input headers are consumed literally; all unread constraint bits retain
their original order and no tape contains an implicit runtime number. -/
def headersInTime (C q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label C) (.headerRead 0) (some (.headerStart 1))
    (program C) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabet (by decide)
    (.headerStart 1 : Label C) (.headerRead 1) (some (.headerStart 2))
    (program C) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label C) (.headerRead 2) (some (.scale 0))
    (program C) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  simpa only [encodeWords, List.nil_append, List.append_assoc, machine, FinTM2.step,
    FinTM2.Cfg, initialState]
    using! ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program C))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

end MaxCutGames.Explicit.MachineUniformHeaders

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate tape-space bounds derived from actual successful machine
prefixes, and their use in the separately checked physical finalizer. -/

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

namespace MaxCutGames.Explicit.MachineUniformRun

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MachineUniformProgram

def scaleInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩
      (some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩)
      (2 * (Q + 1) + 1) where
  steps := 2 * (Q + 1) + 1
  evals_in_steps := by
    change (MachineComposition.advance (machine C).step)^[2 * (Q + 1) + 1]
      (some ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩) =
      some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
    have h := MachineUnaryAffineAt.seededAffineTrace Tape.occurrences .affineScratch
      .newOccurrences (by decide) (by decide) (by decide) C 0
      (.scale 0 : Label C) (.scale 1) (.scale 2) (some (emitEntry C))
      (program C) rfl rfl rfl (MachineUniformHeaders.resultTapes n q Q body)
      Q [] (by simp [MachineUniformHeaders.resultTapes])
      (by simp [MachineUniformHeaders.resultTapes]) ((), ()) none
    simpa only [machine, FinTM2.step, FinTM2.Cfg,
      initialState, afterScale,
      show MachineUniformHeaders.resultTapes n q Q body .newOccurrences = [] from rfl,
      Nat.add_zero, List.append_nil] using! h
  steps_le_m := Nat.le_refl _

def emitInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      (3 * (n + q + C * Q + 3 + C * body.length) + 3 * (C + 3) + 1) := by
  have h := MachineFieldTemplate.phaseInTime (tokens C) emitField
    Tape.copyScratch .accumulator
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide) (by decide)
    (Label.emit (C := C)) (some .finishStart) (program C) (fun _ => rfl)
    (afterScale C n q Q body) (by simp [afterScale, MachineUniformHeaders.resultTapes])
    initialState
  simpa only [machine, FinTM2.step, FinTM2.Cfg, emitEntry,
    MachineFieldTemplate.reset, initialState,
    template_output, template_copiedLength, afterEmit,
    show (tokens C).length = C + 3 by simp [tokens]] using! h

def prefixInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      ((prefixPolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let first := MachineUniformHeaders.headersInTime C q n Q body
  let second := scaleInTime C n q Q body
  let third := emitInTime C n q Q body
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, input_length]
  have hcopy : n + q + C * Q + 3 + C * body.length ≤
      (C + 1) * (n + q + Q + 3 + body.length) := by nlinarith
  nlinarith

noncomputable def timePolynomial (C : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine C) clearKeys.length (prefixPolynomial C + 1)

theorem haltList_eq (C : Nat) (bits : List Bool) :
    haltList (machine C) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes] <;> rfl

def finishStartInTime (C : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program C .finishStart) initialState base) = _
    rfl
  steps_le_m := Nat.le_refl _

end MaxCutGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ProductTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

/-!
Concrete numbered, full-table output for the v2 four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace MaxCutGames.Explicit.SubdivisionTarget

open MaxCutGames.Foundations Target
open MachineOutputContract
open scoped BigOperators

/-- The five physical fields consumed by the checked row-emission phase. -/
def vertexFields {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    Fin 5 → Fin (H.vertices + 3 * H.constraints.length) :=
  ![numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].source)),
    numericVertexEquiv _ _ (Sum.inr (e, false)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inr e)),
    numericVertexEquiv _ _ (Sum.inr (e, true)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].target))]

theorem vertexFields_val {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (j : Fin 5) :
    (vertexFields H e j).val = MachineSubdivisionRows.subdivisionVertexWords
      H.vertices H.constraints.length H.constraints[e].source.val
        H.constraints[e].target.val e.val j := by
  fin_cases j <;> simp [vertexFields, MachineSubdivisionRows.subdivisionVertexWords]

/-- Four consecutive semantic rows are exactly the four full-table rows emitted
by the machine phase, including the inverse table in the final row. -/
theorem rows_eq {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    List.ofFn (fun i : Fin 4 => ProductTarget.row (Subdivision.game (ofInstance H))
      (numericVertexEquiv H.vertices H.constraints.length)
      (numericEdgeEquiv H.constraints.length) (tables H)
      ((numericEdgeEquiv H.constraints.length).symm (e, i))) =
    MachineSubdivisionRows.rows (vertexFields H e) H.constraints[e].permutation := by
  simp [List.ofFn_succ, ProductTarget.row, Subdivision.game, Subdivision.left,
    Subdivision.right, ofInstance, tables, vertexFields, MachineSubdivisionRows.rows]

end MaxCutGames.Explicit.SubdivisionTarget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SubdivisionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact whole-output serialization of four-edge subdivision. The input occurrence
at index `e` produces the four adjacent rows at `4e,4e+1,4e+2,4e+3`.
The bit formula uses the same complete row output as the checked machine phase.
-/

namespace MaxCutGames.Explicit.SubdivisionEncoding

open MaxCutGames.Foundations Target Complexity
open SubdivisionTarget

theorem subdivide_constraints {q : Nat} (H : Instance q) :
    (subdivide H).constraints =
      (List.ofFn (fun e : Fin H.constraints.length =>
        MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation)).flatten := by
  change List.ofFn _ = _
  rw [List.ofFn_mul']
  congr 1
  apply congrArg List.ofFn
  funext e
  rw [← rows_eq H e]
  apply congrArg List.ofFn
  funext i
  congr 1
  apply Fin.ext
  simp only [numericEdgeEquiv_symm_val]

theorem subdivide_constraints_flatMap {q : Nat} (H : Instance q) :
    (subdivide H).constraints = (List.finRange H.constraints.length).flatMap
      (fun e => MachineSubdivisionRows.rows (vertexFields H e)
        H.constraints[e].permutation) := by
  rw [subdivide_constraints, List.ofFn_eq_map]
  rfl

/-- Header and complete row words, in the original input occurrence order. -/
theorem subdivide_gameWords {q : Nat} (H : Instance q) :
    gameWords (subdivide H) =
      [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        (MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation).flatMap constraintWords) := by
  change [H.vertices + 3 * H.constraints.length, q, (subdivide H).constraints.length] ++
    (subdivide H).constraints.flatMap
      (@constraintWords (H.vertices + 3 * H.constraints.length) q) = _
  rw [subdivide_length, subdivide_constraints_flatMap, List.flatMap_assoc]

/-- Exact output bytes for the whole controller to emit: one header followed by
the verified four-row phase once per original occurrence. -/
theorem subdivide_gameBits {q : Nat} (H : Instance q) :
    gameBits (subdivide H) =
      encodeWords [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (vertexFields H e) H.constraints[e].permutation) := by
  rw [gameBits, subdivide_gameWords, encodeWords_append, encodeWords_flatMap_inline_SubdivisionEncoding]
  rfl

end MaxCutGames.Explicit.SubdivisionEncoding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionDynamicRows
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Four-edge subdivision row emission with a physical permutation-table field.

The program depends only on the fixed identity table. Five saved endpoint words
and the entire final forward permutation table are physical tape contents. In
particular an input-dependent permutation is not inserted into a program label
or literal instruction. The last row is oriented `v → r`; for binary-vector
translations its table equals the inverse table of the original `u → v` edge.
-/

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

namespace MaxCutGames.Explicit.MachineSubdivisionProgram

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction

/-- A fixed finite program: the table reader counts only `q` delimiters in
finite control, while all unbounded integers are physical unary tape contents. -/
def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .initialize_ i 0 =>
      match (initOp i).seed with
      | some offset => MachineUnaryAffineAt.seed (initOp i).destination offset (.initialize_ i 1)
      | none => .goto (fun _ => .initialize_ i 1)
  | .initialize_ i 1 => MachineUnaryAffineAt.scan (initOp i).source .affineScratch
      (initOp i).destination (initOp i).coefficient (.initialize_ i 1) (.initialize_ i 2)
  | .initialize_ i 2 => MachineTransfer.loopAt .affineScratch (initOp i).source
      id false (.initialize_ i 2) (some (initNext i))
  | .emitHeader label => MachineFieldTemplate.instruction (headerTokens q)
      newHeaderField .copyScratch .accumulator Label.emitHeader (some .guard) label
  | .guard => MachineUnaryCounter.guard .remaining .startU .finishStart
  | .startU => SourceMachine.fieldStart .u .readU
  | .readU => SourceMachine.fieldLoop .input .u .readU (some .startV)
  | .startV => SourceMachine.fieldStart .v .readV
  | .readV => SourceMachine.fieldLoop .input .v .readV (some (.readTable 0))
  | .readTable completed =>
      if h : completed.val < q then
        .pop .input (fun state head => (state.1, head))
          (.push .permutationReverse (fun state => state.2.getD false)
            (.branch (fun state => state.2.getD false)
              (.goto fun _ => .readTable completed)
              (.load (fun state => (state.1, none))
                (.goto fun _ => .readTable ⟨completed.val + 1, by omega⟩))))
      else .load (fun state => (state.1, none)) (.goto fun _ => .reverseTable)
  | .reverseTable => MachineTransfer.loopAt .permutationReverse .permutation
      id false .reverseTable (some (rowEntry q))
  | .emitRows label => MachineFieldTemplate.instruction (rowTokens q)
      rowField .copyScratch .accumulator Label.emitRows (some .drainU) label
  | .drainU => MachineDrain.drain .u .drainU (some .drainV)
  | .drainV => MachineDrain.drain .v .drainV (some .drainPermutation)
  | .drainPermutation => MachineDrain.drain .permutation .drainPermutation (some .increment)
  | .increment => .push .middle (fun _ => true)
      (.push .first (fun _ => true) (.push .first (fun _ => true)
        (.push .last (fun _ => true) (.push .last (fun _ => true)
          (.load (fun _ => initialState) (.goto fun _ => .guard))))))
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program q

end MaxCutGames.Explicit.MachineSubdivisionProgram

/-! Exact execution of the three input-header reads of subdivision. -/

namespace MaxCutGames.Explicit.MachineSubdivisionHeaders

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineSubdivisionProgram

theorem initList_eq (q : Nat) (bits : List Bool) :
    initList (machine q) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

/-- The input headers are consumed literally; all unread constraint bits retain
their original order and no tape contains an implicit runtime number. -/
def headersInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.initialize_ 0 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label q) (.headerRead 0) (some (.headerStart 1))
    (program q) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabetHeader (by decide)
    (.headerStart 1 : Label q) (.headerRead 1) (some (.headerStart 2))
    (program q) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label q) (.headerRead 2) (some (.initialize_ 0 0))
    (program q) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  simpa only [encodeWords, List.nil_append, List.append_assoc, machine, FinTM2.step, FinTM2.Cfg, initialState]
    using! ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program q))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.initialize_ 0 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

end MaxCutGames.Explicit.MachineSubdivisionHeaders

/-! Physical header arithmetic and private-vertex initialization. -/

namespace MaxCutGames.Explicit.MachineSubdivisionInit

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

theorem operationTrace (q : Nat) (i : Fin 9) (base : Tape → List Bool) (a b : Nat)
    (sourceWord : base (initOp i).source = encodeWord a)
    (scratchEmpty : base .affineScratch = [])
    (destinationWord : base (initOp i).destination = priorWord (initOp i).seed b) :
    (MachineComposition.advance (machine q).step)^[2 * (a + 1) + 1]
      (some ⟨some (.initialize_ i 0), initialState, base⟩) =
      some ⟨some (initNext i), initialState,
        Function.update base (initOp i).destination
          (encodeWord ((initOp i).coefficient * a + (initOp i).seed.getD b))⟩ := by
  cases seedValue : (initOp i).seed with
  | some offset =>
    have run := MachineUnaryAffineAt.seededAffineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient offset
      (.initialize_ i 0 : Label q) (.initialize_ i 1) (.initialize_ i 2)
      (some (initNext i)) (program q)
      (by simp [program, seedValue]) rfl rfl base a []
      (by simpa using sourceWord) scratchEmpty ((), ()) none
    have hd : base (initOp i).destination = [] := by
      simpa [priorWord, seedValue] using destinationWord
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState, hd, List.append_nil, seedValue,
      Option.getD_some] using! run
  | none =>
    have hd : base (initOp i).destination = encodeWord b := by
      simpa [priorWord, seedValue] using destinationWord
    have frame (word : List Bool) :
        MachineUnaryAffineAt.tapes (initOp i).source Tape.affineScratch
          (initOp i).destination base (encodeWord a ++ []) [] word =
        Function.update base (initOp i).destination word := by
      simp only [List.append_nil]
      rw [← sourceWord, ← scratchEmpty]
      simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes,
        Function.update_eq_self]
    have run := MachineUnaryAffineAt.affineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient (.initialize_ i 1 : Label q) (.initialize_ i 2)
      (some (initNext i)) (program q) rfl rfl base a b [] [] ((), ()) none
    rw [frame, frame] at run
    simp only [List.append_nil, ← hd, Function.update_eq_self] at run
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine q).step)^[2 * (a + 1)]
      (some (TM2.stepAux (program q (.initialize_ i 0)) initialState base)) = _
    simp only [program, seedValue, TM2.stepAux]
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState, seedValue, Option.getD_none] using! run

def prefixInTime (q n Q : Nat) (body : List Bool) (r : Nat) (hr : r ≤ 9) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize_ 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (atStage q r), initialState, frame n q Q body r⟩)
      (r * stageCost n Q) := by
  induction r with
  | zero =>
    refine { steps := 0, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp [atStage, frame]
    · simp
  | succ r ih =>
    have hlt : r < 9 := by omega
    let i : Fin 9 := ⟨r, hlt⟩
    have before := ih (by omega)
    have opTrace := operationTrace q i (frame n q Q body r)
      (sourceValue n Q i) (beforeValue n i)
      (frame_source n q Q body i) (frame_scratch n q Q body i)
      (frame_destination n q Q body i)
    have op : StateTransition.EvalsToInTime (machine q).step
        ⟨some (atStage q r), initialState, frame n q Q body r⟩
        (some ⟨some (atStage q (r + 1)), initialState, frame n q Q body (r + 1)⟩)
        (stageCost n Q) := {
      steps := 2 * (sourceValue n Q i + 1) + 1
      evals_in_steps := by
        change (MachineComposition.advance (TM2.step (program q)))^[_] _ = _
        simpa only [FinTM2.step, FinTM2.Cfg, machine, atStage, hlt,
          ↓reduceDIte, i, initNext_eq_atStage, frame, afterValue] using! opTrace
      steps_le_m := by
        have bound := sourceValue_le n Q i
        dsimp [stageCost]
        omega }
    have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ before op
    exact {
      toEvalsTo := joined.toEvalsTo
      steps_le_m := by
        calc
          joined.steps ≤ stageCost n Q + r * stageCost n Q := joined.steps_le_m
          _ = (r + 1) * stageCost n Q := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
    }

/-- The actual initialized loop counters and fresh numeric vertex IDs are
proved outputs of unary arithmetic, including the runtime vertex header. -/
def initializeInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize_ 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, resultTapes n q Q body⟩)
      (9 * stageCost n Q) := by
  simpa only [atStage, show ¬ (9 < 9) by omega, ↓reduceDIte, final_frame]
    using prefixInTime q n Q body 9 (by omega)

end MaxCutGames.Explicit.MachineSubdivisionInit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CanonicalWordTemplate
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

/-- Exact body serialization of general canonical data. -/
theorem eval_data {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d) :
    evalTemplate (sourceFields occ names) (template z a (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.data occ names rhs z a).1.2,
        (ActualCanonical.data occ names rhs z a).2) := by
  change
    vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        evalTemplate (sourceFields occ names) (recordsList a (List.ofFn id)) =
      vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        (List.ofFn (fun j => ActualCanonical.record names (occ j) (a j))).flatMap recordWords
  rw [eval_recordsList, List.map_ofFn]
  rfl

theorem eval_canonical {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (X : ActualHomogeneous.E k →ₗ[F2] Ambient s d) :
    evalTemplate (sourceFields occ names)
        (template (X (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple X)
          (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.canonical occ names rhs X).1.2,
        (ActualCanonical.canonical occ names rhs X).2) :=
  eval_data occ names rhs _ _

theorem eval_actualQuery (S : ActualSource.Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    evalTemplate (sourceFields q.1 (ActualGame.names S))
        (template (q.2 (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple q.2)
          (fun j => ActualGame.rhs S (q.1 j))) =
      bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  eval_canonical q.1 (ActualGame.names S) (ActualGame.rhs S) q.2

end MaxCutGames.Reduction.CanonicalBodyTemplate

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CloneMachineModel
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine word emission in the actual clone-table machine

The shared machine keeps its context fixed while copying one saved word. Its
finite transducer therefore acts by a fixed symbol substitution. The lemmas
below identify that substitution with the established unary encoding of
`offset + scale * value`, including all header and equation-field contexts.
Scale, offset, and the triple-table length remain symbolic.
-/

namespace MaxCutGames.Reduction.MachineAddressHeaders

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineComposition

namespace Prefix

variable {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem atReadStart (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readStart r) =
      SourceMachine.fieldStart (destination slots r) (labels (readLoop r)) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadLoop (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readLoop r) =
      SourceMachine.fieldLoop (slots 1) (destination slots r) (labels (readLoop r))
        (some (labels (readStart (r + 1)))) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadDone (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    statement (σ := σ) slots labels exit (readStart 2) =
      SourceFieldArray.finish (slots 1) (some (labels .clear)) := by
  simp [statement, readStart]

theorem clear_readTapes (slots : Fin 5 ↪ K) (base : K → List Bool)
    (n m : Nat) (suffix : List Bool) :
    Function.update (readTapes slots base n m suffix) (slots 1) [] =
      resultTapes slots base n m := by
  funext tape
  by_cases hw : tape = slots 1
  · subst tape
    simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
      SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
  · by_cases hn : tape = slots 2
    · subst tape
      simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
        SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
    · by_cases hm : tape = slots 3
      · subst tape
        simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
      · simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff, hw, hn, hm]

/-- Actual copying, two-field extraction, and complete disposal of the work copy. -/
def inTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base (slots 0) = encodeWords [n, m] ++ suffix)
    (hwork : base (slots 1) = []) (hscratch : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (3 * (base (slots 0)).length + 6) := by
  have copying := MachineCopy.copyInTime (slots 0) (slots 1) (slots 4)
    (by simp [slots.injective.eq_iff]) (by simp [slots.injective.eq_iff])
    (by simp [slots.injective.eq_iff]) false (labels .copyOut) (labels .copyBack)
    (some (labels (readStart 0))) program (atLabels .copyOut) (atLabels .copyBack)
    base hscratch (ambient, ()) register
  have hc : Function.update base (slots 1) (base (slots 0) ++ base (slots 1)) =
      copied slots base := by simp [copied, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime (slots 1) (destination slots)
    (fun r => labels (readStart r)) (fun r => labels (readLoop r)) (some (labels .clear))
    program (copied slots base) 0 [n, m] suffix
    (by
      intro r hr
      simp only [destination]
      split <;> simp [slots.injective.eq_iff])
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readStart r)).trans (atReadStart slots labels exit r (by simpa using hr)))
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readLoop r)).trans (atReadLoop slots labels exit r (by simpa using hr)))
    (by simpa using (atLabels (readStart 2)).trans (atReadDone slots labels exit))
    (by simp [copied, hinput]) (ambient, ()) none
  have draining := MachineDrain.drainInTime (slots 1) (labels .clear) exit program
    (atLabels .clear) (readTapes slots base n m suffix) (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readTapes] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readTapes_work, hinput]
    simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega

end Prefix

noncomputable section

namespace Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type}

variable [DecidableEq K]

def preparedBase (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update base (control slots .baseValue) (encodeWord (radix s d n m))

end Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

theorem prefixResult_coefficient (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) (i : Arithmetic.Coefficients k s d noiseCount) :
    Prefix.resultTapes (prefixSlots slots) base n m (arithmeticSlots slots (.inr i)) =
      base (arithmeticSlots slots (.inr i)) := by
  apply Prefix.resultTapes_other <;>
    simp [prefixSlots, prefixLocal_apply, arithmeticSlots, slots.injective.eq_iff]

end

end MaxCutGames.Reduction.MachineAddressHeaders

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTemplateAddress
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed canonical-word template followed by actual radix-address execution.
The program is determined by the fixed tokens and tape layout. Numeric field
values enter only the tape invariants and execution theorem, never the labels. -/

namespace MaxCutGames.Reduction.MachineTemplateAddress

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

section Execution

variable (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
variable (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ l, P (place l) = instruction tokens slots place exit l)

include atInstruction

omit [DecidableEq K] in
theorem parse_atStart (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.startLabel width r))) =
      SourceMachine.fieldStart (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atLoop (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.loopLabel width r))) =
      SourceMachine.fieldLoop (slots .forward) (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r)))
        (some (place (parseLabel (SourceFieldArray.startLabel width (r + 1))))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atDone :
    P (place (parseLabel (SourceFieldArray.startLabel width width))) =
      SourceFieldArray.finish (slots .forward) (some (place (hornerLabel .start))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel]

end Execution

theorem phaseSteps_le_timePolynomial (tokens : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (slots (.field j))).length ≤ M)
    (wordsBound : (encodeWords values).length ≤ M) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → digits values i ≤ M) :
    phaseSteps tokens slots base B values ≤ (timePolynomial tokens.length width).eval M := by
  have hcopied := copiedLength_le_inline_MachineTemplateAddress tokens (fun j => base (slots (.field j))) M fieldsBound
  have htemplate := MachineFieldTemplate.templateSteps_le tokens (fun j => base (slots (.field j)))
  have hhorner := MachineHorner.steps_le_timePolynomial B (digits values) width M radixBound digitBound
  have hselected : ∀ tape ∈ chosen slots, (afterHorner slots base B values tape).length ≤ M + 1 := by
    intro tape ht
    obtain ⟨i, rfl⟩ := (mem_chosen slots tape).mp ht
    have heq : afterHorner slots base B values (slots (.digit i)) =
        encodeWord (digits values i.val) := by
      simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        Function.update_of_ne (slots.injective.ne (show Tape.digit i ≠ Tape.output by simp))]
      exact parsedTapes_digit slots base values hlen clean i
    rw [heq]
    simpa only [encodeWord, List.length_append, List.length_replicate, List.length_singleton] using
      Nat.add_le_add_right (digitBound i.val i.isLt) 1
  have hsum := lengthSum_le_inline_MachineTemplateAddress (chosen slots) (afterHorner slots base B values) (M + 1) hselected
  have hcleanup := MachineDrainMany.steps_le (chosen slots) (afterHorner slots base B values)
  have hchosen : (chosen slots).length = width := by simp [chosen]
  rw [hchosen] at hsum hcleanup
  have hparse := SourceFieldArray.sequence_time_eq_length values
  rw [hlen] at hparse
  rw [timePolynomial_eval]
  unfold phaseSteps
  rw [hlen]
  nlinarith

end MaxCutGames.Reduction.MachineTemplateAddress

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

namespace MaxCutGames.Reduction.MachineAddressEdge

open Turing
open MaxCutGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem work_ne_output (slots : Tape q width ↪ K) :
    workTape slots ≠ outputTape slots := address_ne_output slots _

omit [DecidableEq K] in
theorem temp_ne_work (slots : Tape q width ↪ K) :
    tempTape slots ≠ workTape slots := slots.injective.ne (by simp)

structure Clean (slots : Tape q width ↪ K) (base : K → List Bool) : Prop where
  address : MachineTemplateAddress.Clean (addressSlots slots) base
  work : base (workTape slots) = []

theorem appended_other (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) (tape : K) (hne : tape ≠ outputTape slots) :
    appended slots base bits tape = base tape :=
  MachineFieldTemplate.outputTapes_other _ _ _ _ hne

theorem appended_append (slots : Tape q width ↪ K) (base : K → List Bool)
    (first second : List Bool) :
    appended slots (appended slots base first) second = appended slots base (first ++ second) :=
  MachineFieldTemplate.outputTapes_append _ _ _ _

theorem Clean.appended (slots : Tape q width ↪ K) (base : K → List Bool)
    (clean : Clean slots base) (bits : List Bool) : Clean slots (appended slots base bits) := by
  constructor
  · constructor
    · simpa only [appended_address] using clean.address.reversed
    · simpa only [appended_address] using clean.address.forward
    · simpa only [appended_address] using clean.address.copyScratch
    · simpa only [appended_address] using clean.address.accA
    · simpa only [appended_address] using clean.address.accB
    · simpa only [appended_address] using clean.address.counter
    · simpa only [appended_address] using clean.address.hornerScratch
    · intro j; simpa only [appended_address] using clean.address.digit j
  · simpa only [workTape, appended_address] using clean.work

def phaseSteps (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool)
    (B C : Nat) (leftValues rightValues : List Nat) : Nat :=
  MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues +
    MachineTemplateAddress.phaseSteps right (addressSlots slots)
      (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues +
    CanonicalAddress.radix B leftValues + CanonicalAddress.radix B rightValues + 4 * C + 12

theorem addressResult_eq (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    MachineTemplateAddress.resultTapes (addressSlots slots) base value =
      Function.update base (workTape slots) (encodeWord value ++ base (workTape slots)) := rfl

theorem transfer_result (slots : Tape q width ↪ K) (base : K → List Bool)
    (value : Nat) (empty : base (workTape slots) = []) :
    MachineTransfer.tapesAt (workTape slots) (outputTape slots)
      (MachineTemplateAddress.resultTapes (addressSlots slots) base value) []
      (((MachineTemplateAddress.resultTapes (addressSlots slots) base value) (workTape slots)).reverse.map id ++
        (MachineTemplateAddress.resultTapes (addressSlots slots) base value) (outputTape slots)) =
      appended slots base (encodeWord value) := by
  funext tape
  by_cases hw : tape = workTape slots
  · subst tape
    simp [MachineTransfer.tapesAt, addressResult_eq, appended,
      MachineFieldTemplate.outputTapes, work_ne_output, empty]
  · by_cases ho : tape = outputTape slots
    · subst tape
      simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, Ne.symm (work_ne_output slots), empty]
    · simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, hw, ho]

section Execution

variable (left right : List (MachineFieldTemplate.Token q)) (permutation : List Bool)
variable (slots : Tape q width ↪ K)
variable (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
variable (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction left right permutation slots place exit label)

include atInstruction

theorem literalStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (plumbing 6)), state, base⟩ =
      some ⟨exit, MachineFieldTemplate.reset state, appended slots base permutation⟩ := by
  change some (TM2.stepAux (P (place (plumbing 6))) state base) = _
  rw [atInstruction (plumbing 6)]
  simp only [instruction, plumbing, TM2.stepAux]
  rw [stepAux_pushWord]
  cases exit <;> rfl

end Execution

omit [DecidableEq K] in
theorem radix_le_magnitude (B : Nat) (values : List Nat) (width M : Nat)
    (hlen : values.length = width) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → MachineTemplateAddress.digits values i ≤ M) :
    CanonicalAddress.radix B values ≤ (M + 1) ^ width := by
  have h := MachineHorner.value_le B (MachineTemplateAddress.digits values) values.length M
    radixBound (by simpa only [hlen] using digitBound) values.length (Nat.le_refl _)
  rw [MachineTemplateAddress.hornerValue_eq_radix, hlen] at h
  exact h

theorem phaseSteps_le_timePolynomial (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (addressSlots slots (.field j))).length ≤ M)
    (leftWordsBound : (encodeWords leftValues).length ≤ M)
    (rightWordsBound : (encodeWords rightValues).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (leftDigitBound : ∀ i, i < width → MachineTemplateAddress.digits leftValues i ≤ M)
    (rightDigitBound : ∀ i, i < width → MachineTemplateAddress.digits rightValues i ≤ M) :
    phaseSteps left right slots base B C leftValues rightValues ≤
      (timePolynomial left.length right.length width).eval M := by
  have hleft := MachineTemplateAddress.phaseSteps_le_timePolynomial left (addressSlots slots)
    base B leftValues leftLength clean.address M fieldsBound leftWordsBound radixBound leftDigitBound
  have hright := MachineTemplateAddress.phaseSteps_le_timePolynomial right (addressSlots slots)
    (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues
    rightLength (Clean.appended slots base clean _).address M
    (by simpa only [appended_address] using fieldsBound) rightWordsBound radixBound rightDigitBound
  have hlrank := radix_le_magnitude B leftValues width M leftLength radixBound leftDigitBound
  have hrrank := radix_le_magnitude B rightValues width M rightLength radixBound rightDigitBound
  rw [timePolynomial_eval]
  unfold phaseSteps
  omega

end MaxCutGames.Reduction.MachineAddressEdge

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_EquationLookup
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.SourceEquationLookup

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

variable {σ : Type}

theorem atSkip (r : Nat) (hr : r < 4) :
    program (σ := σ) (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 4) :
    program (σ := σ) (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 4) :
    program (σ := σ) (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (σ := σ) (readStart 4) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

/-- The two header fields are physically consumed from the work copy. -/
theorem discardHeadersTrace (base : Tape → List Bool) (variableCount equations : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, equations] ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[variableCount + equations + 2]
      (some ⟨some .headerFirst, (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, equations]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ambient
  simpa [encodeWords_length, headerLabel] using ht

/-- The fixed skip body consumes four complete unary fields and returns to the
same counter guard, preserving the counter and every other tape. -/
theorem discardFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ambient
  simpa [hlen, skipLabel] using ht

/-- Read the selected four fields using the already checked scanner. -/
theorem readFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length + 5]
      (some ⟨some (readStart 0), (ambient, none), base⟩) =
      some ⟨none, (ambient, none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput ambient none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 5 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

/-- Each equation-index bit causes one genuine guard transition and exactly four
field-discard loops. The final zero guard enters the field reader. -/
theorem skipEquationsTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (CloneGap.Equation (Fin n))) (indexSuffix suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      (some ⟨some .guard, (ambient, register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap equationWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), (ambient, none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix ambient register
  | cons equation prior ih =>
    have hencoding : encodeWords ((equation :: prior).flatMap equationWords) ++ suffix =
        encodeWords (equationWords equation) ++ (encodeWords (prior.flatMap equationWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((equation :: prior).flatMap equationWords)).length +
        (equation :: prior).length + 1 =
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
          (encodeWords (equationWords equation)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
        (encodeWords (equationWords equation)).length]
      (TM2.step program ⟨some .guard, (ambient, register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardFourTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
      (equationWords equation) (equationWords_length equation)
      (encodeWords (prior.flatMap equationWords) ++ suffix) (by
        rw [scanTapes_work, hencoding]) ambient
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (equationWords equation)).length]
        (some ⟨some (skipLabel 0), (ambient, none), scanTapes base prior.length indexSuffix
          (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[scanSteps variableCount declaredEquations prior equation]
      (some ⟨some .headerFirst, (ambient, none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredEquations] ++
          (encodeWords (prior.flatMap equationWords) ++
            (encodeWords (equationWords equation) ++ suffix)))⟩) =
      some ⟨none, (ambient, none), outputTapes base equation indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredEquations] ++
        (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))))
    variableCount declaredEquations
    (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))
    (by simp) ambient
  have hs := skipEquationsTrace base prior indexSuffix (encodeWords (equationWords equation) ++ suffix) ambient none
  have hr := readFourTrace
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    (equationWords equation) (equationWords_length equation) suffix (by simp) ambient
  rw [show scanSteps variableCount declaredEquations prior equation =
      ((encodeWords (equationWords equation)).length + 5 +
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1)) +
        (variableCount + declaredEquations + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  exact hr

theorem lookupWithSplitTrace (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior equation]
      (some ⟨some .copyOut, (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩ := by
  have hbits : inputBits F = encodeWords [F.«variables», F.equations.length] ++
      (encodeWords (prior.flatMap equationWords) ++
        (encodeWords (equationWords equation) ++ encodeWords (after.flatMap equationWords))) := by
    simp only [inputBits, inputWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .source .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch ambient register
  have htapes : Function.update base .work (base .source ++ base .work) =
      scanTapes base prior.length indexSuffix (inputBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hsource, hindex, hwork]
  rw [htapes, hsource] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.«variables» F.equations.length prior equation indexSuffix
    (encodeWords (after.flatMap equationWords)) ambient

/-- A polynomial bound on the actual complete copy/skip/read execution. -/
def lookupWithSplitInTime (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) where
  steps := lookupSteps F prior equation
  evals_in_steps := lookupWithSplitTrace F prior equation after hsplit base indexSuffix
    hsource hindex hwork hscratch ambient register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior equation after hsplit

def lookupInTime (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none), outputTapes base F.equations[i.val] indexSuffix
        (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) := by
  have hp : (F.equations.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.equations = F.equations.take i.val ++ F.equations[i.val] :: F.equations.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.equations.take i.val) F.equations[i.val]
    (F.equations.drop (i.val + 1)) hs base indexSuffix hsource
    (by simpa only [hp] using hindex) hwork hscratch ambient register

end MaxCutGames.Reduction.SourceEquationLookup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTuple
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineSourceTuple

open Turing MaxCutGames.Foundations.Complexity
open SourceEncoding
open MachineComposition

variable {width : Nat} {Extra σ : Type}

variable [DecidableEq Extra]

theorem placed_stepAux (j : Fin width) (base : Tape width Extra → List Bool)
    (q : TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (state : (σ × Unit) × Option Bool) (localTapes : SourceEquationLookup.Tape → List Bool) :
    TM2.stepAux (placedStatement j q) state (fill j base localTapes) =
      placedConfiguration j base (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using ih (f state _) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state _) _
  | load f next ih => simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

theorem placed_step (j : Fin width) (base : Tape width Extra → List Bool)
    (a b : TM2.Cfg (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (h : TM2.step SourceEquationLookup.program a = some b) :
    TM2.step program (placedConfiguration j base a) =
      some (placedConfiguration j base b) := by
  cases a with
  | mk l state localTapes =>
    cases l with
    | none => contradiction
    | some l =>
      change some (TM2.stepAux (SourceEquationLookup.program l) state localTapes) = some b at h
      cases Option.some.inj h
      change some (TM2.stepAux (placedStatement j (SourceEquationLookup.program l))
        state (fill j base localTapes)) = _
      rw [placed_stepAux]

noncomputable def placedLookupInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((ambient, ()), register), base⟩
      (some ⟨some (.clearWork j), ((ambient, ()), none), lookupOutput j F i base suffix⟩)
      (4 * (inputBits F).length + 8) := by
  have h := SourceEquationLookup.lookupInTime F i (base ∘ place j) suffix
    hsource hindex hwork hscratch (ambient, ()) register
  have lifted := liftExecutionInTime (TM2.step SourceEquationLookup.program) (TM2.step program)
    (placedConfiguration j base) (placed_step j base) h
  simpa only [placedConfiguration, placedLabel, fill_self,
    SourceEquationLookup.timePolynomial_eval, lookupOutput] using lifted

noncomputable def coordinateInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : base (.savedIndex j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((ambient, ()), register), base⟩
      (some ⟨some (nextLabel j), ((ambient, ()), none), coordinateOutput j F.equations[i.val] base⟩)
      (6 * (inputBits F).length + 4 * (base (.savedIndex j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.savedIndex j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy (ambient, ()) register
  have copied_eq : Function.update base .index (base (.savedIndex j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hsource)
    (by simpa [copied, copiedTapes] using hsavedIndex)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) ambient none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded (ambient, ()) none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) (ambient, ()) none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords) := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_index]
  have hc : suffix.length ≤ (base (.savedIndex j)).length := by
    rw [hsavedIndex, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

noncomputable def prefixInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ width) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨some (labelAt r), ((ambient, ()), none), stageTapes F tuple base r⟩)
      (r * (6 * (inputBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < width := by omega
    let j : Fin width := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape width Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.savedIndex j) = base (.savedIndex j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hsource)
      (by rw [hc]; exact hsavedIndex j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) ambient none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((ambient, ()), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((ambient, ()), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (inputBits F).length + 4 * C + 20) := by
      refine { steps := one.steps, evals_in_steps := ?_, steps_le_m := ?_ }
      · simpa only [labelAt, dite_eq_left hru, nextLabel_eq, j, stageTapes, before] using
          one.evals_in_steps
      · apply Nat.le_trans one.steps_le_m
        rw [hc]
        have hs := hsize j
        omega
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

noncomputable def loadInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (6 * (inputBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hsource hsavedIndex hsize
    hindex hwork hscratch hcopy width (Nat.le_refl _) ambient
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

/-- Actual odometer digits have empty suffixes. The resulting complete loader
runs in a polynomial whose coefficients depend only on the fixed repetition k. -/
noncomputable def loadUnaryInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (inputBits F).length hsource
    (by simpa only [List.append_nil] using hsavedIndex)
    (by
      intro j
      rw [hsavedIndex j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := equations_length_le_input F
      omega)
    hindex hwork hscratch hcopy ambient
  have he : 6 * (inputBits F).length + 4 * (inputBits F).length + 20 =
      10 * (inputBits F).length + 20 := by omega
  simpa only [he] using run

omit [DecidableEq Extra] in
theorem output_name (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) (s : Fin 3) :
    stageTapes F tuple base width (nameField j s) =
      encodeWord (equationName F.equations[(tuple j).val] s) ++ base (nameField j s) := by
  rw [nameField, stageTapes_field, ite_eq_left j.isLt, equationWords_name]

/-- A caller shares this complete tape arena and state, mapping only labels and
the final continuation. All saved occurrence IDs remain available to its body. -/
noncomputable def placedLoadUnaryInTime {Λ : Type}
    (labels : Label width → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ ((σ × Unit) × Option Bool))
    (atLabels : ∀ l, target (labels l) = MachineSubroutine.statement labels exit (program l))
    (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt 0)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) :=
  MachineSubroutine.execution labels exit program target atLabels
    (loadUnaryInTime F tuple base hsource hsaved hindex hwork hscratch hcopy ambient)

end MaxCutGames.Reduction.MachineSourceTuple

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CanonicalBodyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower a complete canonical-body template to the actual field-template
machine. There are four saved fields per query position, numbered by
`field + 4 * position`. The template constants depend only on finite coefficient
and RHS data; names and occurrence identifiers remain saved tape contents. -/

namespace MaxCutGames.Reduction.AddressMachineSpace

open MaxCutGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

theorem tupleOutput_headerTape (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple base k (headerTape k s d noiseCount c) =
      base (headerTape k s d noiseCount c) :=
  MachineSourceTuple.stageTapes_frame F tuple base k _
    (by simp [headerTape])
    (by simp [headerTape])
    (by intros; simp [headerTape])

end MaxCutGames.Reduction.AddressMachineSpace

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressTupleLoaded
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Integration.AddressTupleLoaded

open MaxCutGames.Reduction MaxCutGames.Foundations.Complexity

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

variable {k s d noiseCount : Nat}

/-- The explicit field assignment performed by all `k` real lookup stages.
Unrelated tapes, including the loader's empty index/work tapes, are unchanged. -/
def fieldAssignment (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool
  | .field j slot => encodeWord
      ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ++
        baseArena (.field j slot)
  | tape => baseArena tape

theorem stageTapes_eq (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hindex : baseArena .index = []) (hwork : baseArena .work = []) :
    MachineSourceTuple.stageTapes F tuple baseArena k = fieldAssignment F tuple baseArena := by
  funext tape
  cases tape with
  | index => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).1.trans hindex.symm
  | work => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).2.trans hwork.symm
  | field j slot =>
    simp only [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, fieldAssignment]
  | source =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | scratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | copyScratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | savedIndex j =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | extra value =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)

theorem loaded_field (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.field j slot) =
      encodeWord ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) := by
  rw [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, hempty, List.append_nil]

theorem loaded_extra (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.extra extra) = baseArena (.extra extra) :=
  MachineSourceTuple.stageTapes_frame F tuple baseArena k _
    (by simp) (by simp) (by intros; simp)

theorem loaded_header (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.headerTape k s d noiseCount header) =
        baseArena (AddressMachineSpace.headerTape k s d noiseCount header) :=
  AddressMachineSpace.tupleOutput_headerTape k s d noiseCount F tuple baseArena header

theorem loaded_radix (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (B : Nat)
    (hB : baseArena (AddressMachineSpace.headerTape k s d noiseCount .baseValue) = encodeWord B) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        .radix) = encodeWord B := by
  rw [AddressMachineSpace.addressSlots_radix, loaded_header, hB]

theorem loaded_capacity (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (C : Nat)
    (hC : baseArena (AddressMachineSpace.headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.capacityTape (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) =
        encodeWord C := by
  rw [AddressMachineSpace.addressSlots_capacity, loaded_header, hC]

theorem loaded_privateAddress (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.privateAddress k s d noiseCount tape) =
        baseArena (AddressMachineSpace.privateAddress k s d noiseCount tape) :=
  loaded_extra F tuple baseArena _

/-- Cleanliness of the actual edge machine is preserved by the actual loader.
All of these local work tapes occupy the private disjoint arena block. -/
theorem loaded_clean (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (clean : MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      baseArena) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      (MachineSourceTuple.stageTapes F tuple baseArena k) := by
  constructor
  · constructor
    · exact (loaded_privateAddress F tuple baseArena .reversed).trans clean.address.reversed
    · exact (loaded_privateAddress F tuple baseArena .forward).trans clean.address.forward
    · exact (loaded_privateAddress F tuple baseArena .copyScratch).trans clean.address.copyScratch
    · exact (loaded_privateAddress F tuple baseArena .accA).trans clean.address.accA
    · exact (loaded_privateAddress F tuple baseArena .accB).trans clean.address.accB
    · exact (loaded_privateAddress F tuple baseArena .counter).trans clean.address.counter
    · exact (loaded_privateAddress F tuple baseArena .hornerScratch).trans clean.address.hornerScratch
    · intro j
      exact (loaded_privateAddress F tuple baseArena (.digit j)).trans (clean.address.digit j)
  · exact (loaded_privateAddress F tuple baseArena .output).trans clean.work

theorem loaded_name (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 3) :
    MachineSourceTuple.stageTapes F tuple baseArena k (MachineSourceTuple.nameField j slot) =
      encodeWord (MachineSourceTuple.equationName F.equations[(tuple j).val] slot) := by
  rw [MachineSourceTuple.output_name]
  change _ ++ baseArena (.field j (MachineSourceTuple.nameSlot slot)) = _
  rw [hempty, List.append_nil]

theorem loaded_occurrence (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.savedIndex j) = encodeWord (tuple j).val :=
  MachineSourceTuple.output_savedIndex_unary F tuple baseArena hsaved j

/-- The three names and the distinct saved occurrence field are exact unary
values; the RHS remains on its separate field tape. -/
theorem loaded_canonicalField (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.canonicalField k s d noiseCount j slot) =
        encodeWord (canonicalValues F tuple j slot) := by
  fin_cases slot
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 0
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 1
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 2
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields] using
      loaded_occurrence F tuple baseArena hsaved j

/-- Literal input function used by the generic field-template machine. -/
theorem loaded_savedFields (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) :
    (fun i => MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (.field i))) = CanonicalBodyMachine.savedFields (canonicalValues F tuple) := by
  funext i
  change MachineSourceTuple.stageTapes F tuple baseArena k
    (AddressMachineSpace.canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2) = _
  exact loaded_canonicalField F tuple baseArena hsaved hempty _ _

end MaxCutGames.Integration.AddressTupleLoaded

namespace MaxCutGames.Integration.AddressTupleCleanup

open Turing MaxCutGames.Reduction MaxCutGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

/-- Proof-side cost on the shared arena. Its arithmetic-header tape dimensions
use the fixed polynomial coefficient representation in `PolynomialMachine`.
The executable drain list, entry, and instructions do not evaluate this cost. -/
noncomputable abbrev steps (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.steps (loadedFields k s d noiseCount) base

noncomputable abbrev budget (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.lengthSum (loadedFields k s d noiseCount) base + 4 * k

theorem steps_le (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    steps k s d noiseCount base ≤ budget k s d noiseCount base := by
  simpa only [loadedFields_length] using
    MachineDrainMany.steps_le (loadedFields k s d noiseCount) base

end MaxCutGames.Integration.AddressTupleCleanup

/-!
# The exact frame after a tuple body and its field cleanup

Loading replaces the initially empty equation-field tapes. Appending writes
only the shared reversed-output header, which is outside those fields. The
actual field drains therefore restore the original arena with precisely the
same appended bytes. Saved occurrence indices and the odometer survive.
-/

namespace MaxCutGames.Integration.AddressTupleFrame

open MaxCutGames.Reduction MaxCutGames.Foundations.Complexity

variable {k s d noiseCount : Nat}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

/-- Clearing the physical fields commutes with an append to any other tape. -/
theorem cleared_outputTapes (base : Arena k s d noiseCount → List Bool)
    (output : Arena k s d noiseCount) (bits : List Bool)
    (outside : ∀ j : Fin k, ∀ slot : Fin 4, output ≠ .field j slot) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineFieldTemplate.outputTapes base output bits) =
      MachineFieldTemplate.outputTapes
        (AddressTupleCleanup.cleared k s d noiseCount base) output bits := by
  funext tape
  by_cases h : tape = output
  · subst tape
    rw [AddressTupleCleanup.cleared_outside k s d noiseCount _ output outside,
      MachineFieldTemplate.outputTapes_output, MachineFieldTemplate.outputTapes_output,
      AddressTupleCleanup.cleared_outside k s d noiseCount base output outside]
  · rw [MachineFieldTemplate.outputTapes_other _ output bits tape h]
    change MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount)
        (MachineFieldTemplate.outputTapes base output bits) tape =
      MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount) base tape
    rw [MachineDrainMany.finalTapes_apply, MachineDrainMany.finalTapes_apply,
      MachineFieldTemplate.outputTapes_other base output bits tape h]

/-- The actual edge-output slot is a header tape, not a loaded equation field. -/
theorem cleared_appended (base : Arena k s d noiseCount → List Bool) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          base bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (AddressTupleCleanup.cleared k s d noiseCount base) bits := by
  apply cleared_outputTapes
  intro j slot
  simp [AddressMachineSpace.addressSlots_output, AddressMachineSpace.headerTape,
    ]

/-- Cleanup erases exactly the fields assigned by the tuple loader. -/
theorem cleared_fieldAssignment (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (AddressTupleLoaded.fieldAssignment F tuple base) = base := by
  funext tape
  cases tape <;> simp [AddressTupleLoaded.fieldAssignment, hfields]

theorem cleared_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (MachineSourceTuple.stageTapes F tuple base k) = base := by
  rw [AddressTupleLoaded.stageTapes_eq F tuple base hindex hwork]
  exact cleared_fieldAssignment F tuple base hfields

/-- Exact endpoint of load, edge-byte append, and actual loaded-field cleanup. -/
theorem cleared_appended_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          (MachineSourceTuple.stageTapes F tuple base k) bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        base bits := by
  rw [cleared_appended, cleared_loaded F tuple base hindex hwork hfields]

end MaxCutGames.Integration.AddressTupleFrame

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRhsLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

namespace MaxCutGames.Reduction.MachineOutcomeRows

open Turing
open MaxCutGames.Foundations.Complexity

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

def rowResult (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : K → List Bool :=
  MachineAddressEdge.appended slots base (payload B C values row)

def rowCost (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : Nat :=
  MachineAddressEdge.phaseSteps row.left row.right slots base B C
    (values row).left (values row).right

/-- Exact per-row costs at their actual accumulated output frames. -/
def rowCosts (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) :
    List (Spec q width) → (K → List Bool) → List Nat
  | [], _ => []
  | row :: rows, base => rowCost slots B C values row base ::
      rowCosts slots B C values rows (rowResult slots B C values row base)

structure Invariant (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) : Prop where
  clean : MachineAddressEdge.Clean slots base
  radix : base (MachineAddressEdge.addressSlots slots .radix) = encodeWord B
  capacity : base (MachineAddressEdge.capacityTape slots) = encodeWord C
  correct : ∀ row ∈ rows,
    MachineFieldTemplate.templateOutput row.left
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).left ∧
    MachineFieldTemplate.templateOutput row.right
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).right

theorem Invariant.appended (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) (valid : Invariant slots B C values rows base) (bits : List Bool) :
    Invariant slots B C values rows (MachineAddressEdge.appended slots base bits) := by
  constructor
  · exact MachineAddressEdge.Clean.appended slots base valid.clean bits
  · simpa only [MachineAddressEdge.appended_address] using valid.radix
  · simpa only [MachineAddressEdge.appended_capacity] using valid.capacity
  · intro row hrow
    simpa only [MachineAddressEdge.appended_address] using valid.correct row hrow

theorem appended_nil (slots : MachineAddressEdge.Tape q width ↪ K) (base : K → List Bool) :
    MachineAddressEdge.appended slots base [] = base := by
  simp [MachineAddressEdge.appended, MachineFieldTemplate.outputTapes]

theorem sequence_result (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.resultOf (rowResult slots B C values) rows base =
      MachineAddressEdge.appended slots base (rows.flatMap (payload B C values)) := by
  induction rows generalizing base with
  | nil => simpa only [MachineFiniteSequence.resultOf, List.flatMap_nil] using
      (appended_nil slots base).symm
  | cons row rows ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    exact MachineAddressEdge.appended_append slots base _ _

theorem sequence_steps (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.steps (rowResult slots B C values) (rowCost slots B C values)
      rows base = (rowCosts slots B C values rows base).sum := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [MachineFiniteSequence.steps, rowCosts, List.sum_cons, ih]

def sequenceEntry (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k)
    (place : Label slots rows → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) (selected rows rhs)
    (fun label => place (.inr ⟨rhs, label⟩)) exit

theorem dispatcherStep (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atDispatcher : P (place (.inl ())) = dispatcher slots rows place exit)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool) :
    TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩ =
      some ⟨sequenceEntry slots rows rhs place exit, (((rhs, ambient), ()), none), base⟩ := by
  change some (TM2.stepAux (P (place (.inl ()))) (((rhs, ambient), ()), register) base) = _
  rw [atDispatcher]
  cases rows with
  | nil => cases exit <;> rfl
  | cons row rows => rfl

/-- Sum of fixed row polynomials; the additional constant is the dispatcher.
This proof-side polynomial contains no runtime input field values. -/
noncomputable def timePolynomial (rows : List (Spec q width)) : Polynomial Nat :=
  (rows.map (fun row => MachineAddressEdge.timePolynomial
    row.left.length row.right.length width)).sum + 1

theorem rowCosts_sum_le (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum ≤
      ((rows.map (fun row => MachineAddressEdge.timePolynomial
        row.left.length row.right.length width)).sum).eval M := by
  induction rows generalizing base with
  | nil => simp [rowCosts]
  | cons row rows ih =>
    have bounds := valuesBound row (by simp)
    have first := MachineAddressEdge.phaseSteps_le_timePolynomial row.left row.right
      slots base B C (values row).left (values row).right
      (values row).left_length (values row).right_length clean M fieldsBound
      bounds.1 bounds.2.1 radixBound capacityBound bounds.2.2.1 bounds.2.2.2
    have rest := ih (rowResult slots B C values row base)
      (MachineAddressEdge.Clean.appended slots base clean (payload B C values row))
      (by simpa only [rowResult, MachineAddressEdge.appended_address] using fieldsBound)
      (fun r hr => valuesBound r (List.mem_cons_of_mem row hr))
    simpa only [rowCosts, List.sum_cons, List.map_cons, Polynomial.eval_add, rowCost] using
      Nat.add_le_add first rest

/-- The actual dispatcher-and-rows count is bounded by a fixed polynomial in
explicit tape and digit magnitudes, using the checked edge arithmetic bound. -/
theorem phaseCost_le_timePolynomial (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum + 1 ≤ (timePolynomial rows).eval M := by
  have h := rowCosts_sum_le slots rows base B C values M clean fieldsBound
    radixBound capacityBound valuesBound
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right h 1

end MaxCutGames.Reduction.MachineOutcomeRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable direct addresses for the actual canonical game. Every original
edge occurrence and its translation table is retained, in the same order.
Addresses not representing realized bodies are isolated vertices. No vertex
list, duplicate removal, or inverse enumeration is evaluated by the output. -/

namespace MaxCutGames.Reduction.AddressByteSemantics

open Integration.BinaryLinear Foundations.Complexity ActualSource

def queryRank {k s d : Nat} (base : Nat) (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : Nat :=
  CanonicalAddress.radix base (queryWords fields X b)

def edgeWords {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  [queryRank base fields X b, capacity + queryRank base fields Y b] ++
    permutationWords X Y b

def edgeBits {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Bool :=
  encodeWords (edgeWords base capacity fields X Y b)

theorem queryWords_actual (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    queryWords (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) =
      CanonicalEncoding.bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  CanonicalBodyTemplate.eval_actualQuery S q

theorem queryAddress_false (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d false q).val =
      queryRank (CanonicalAddress.base S.«variables» S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_false_val _

theorem queryAddress_true (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d true q).val =
      AddressGame.bodyCapacity S k s d +
      queryRank (CanonicalAddress.base S.«variables» S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_true_val _

/-- Exact full serialized edge, including every forward permutation image. -/
theorem addressEdge_words (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    constraintWords (AddressGame.addressEdge S k g omega) =
      edgeWords (CanonicalAddress.base S.«variables» S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  unfold constraintWords
  change [ (AddressGame.queryAddress S k s d false (ActualGame.leftQuery S k g omega)).val,
      (AddressGame.queryAddress S k s d true (ActualGame.rightQuery S k g omega)).val ] ++ _ = _
  rw [queryAddress_false, queryAddress_true]
  rfl

theorem addressEdge_bits (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    encodeWords (constraintWords (AddressGame.addressEdge S k g omega)) =
      edgeBits (CanonicalAddress.base S.«variables» S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  rw [addressEdge_words]
  rfl

/-- The actual edge emitter's three payloads concatenate to the codec exactly. -/
theorem edgeBits_split {k s d : Nat} (base capacity : Nat)
    (fields : Fin k → Fin 4 → Nat) (X Y : ActualGame.Map k s d) (b : Fin k → F2) :
    edgeBits base capacity fields X Y b =
      encodeWords [queryRank base fields X b, capacity + queryRank base fields Y b] ++
        encodeWords (permutationWords X Y b) := by
  exact encodeWords_append _ _

end MaxCutGames.Reduction.AddressByteSemantics

namespace MaxCutGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

variable {s d : Nat} {α : Type*}

theorem correct_rows {k s d : Nat} (T : NoiseTables.Table s d)
    (fields : Fin k → Fin 4 → Nat) (b : Fin k → Bool) :
    ∀ spec ∈ MachineOutcomeRows.selected (rows k T) b,
      MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).left ∧
      MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).right := by
  rw [selected_rows]
  intro spec hspec
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hspec
  constructor
  · rw [values_row_left]
    exact row_left_output T p b fields
  · rw [values_row_right]
    exact row_right_output T p b fields

theorem payload_row {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat)
    (B C : Nat) :
    MachineOutcomeRows.payload B C (values fields) (row T p b) =
      AddressByteSemantics.edgeBits B C fields p.1 (rightMap T p) (bitVector b) := by
  unfold MachineOutcomeRows.payload MachineAddressEdge.edgeBits
  rw [values_row_left, values_row_right, AddressByteSemantics.edgeBits_split]
  rfl

theorem rightMap_actual (S : Source) {k s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) (p : Parameter k T) :
    rightMap T p =
      (ActualGame.rightQuery S k (TableReduction.tableSkeleton T) (FixedOutcomes.assemble U p)).2 := rfl

/-- Each static row emits exactly the concrete game's constraint encoding. -/
theorem payload_row_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) (p : Parameter k T) :
    MachineOutcomeRows.payload
        (CanonicalAddress.base S.«variables» S.occurrences s d) (AddressGame.bodyCapacity S k s d)
        (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))
        (row T p (rhsBits S U)) =
      encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
        (FixedOutcomes.assemble U p))) := by
  rw [payload_row, bitVector_rhsBits, rightMap_actual S T U p]
  exact (AddressByteSemantics.addressEdge_bits S k (TableReduction.tableSkeleton T)
    (FixedOutcomes.assemble U p)).symm

theorem tuplePayload_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) :
    (MachineOutcomeRows.selected (rows k T) (rhsBits S U)).flatMap
        (MachineOutcomeRows.payload
          (CanonicalAddress.base S.«variables» S.occurrences s d) (AddressGame.bodyCapacity S k s d)
          (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))) =
      tupleBits S k T U := by
  rw [selected_rows, List.flatMap_map]
  simp only [payload_row_actual, tupleBits]
  rfl

end MaxCutGames.Reduction.AddressOutcomeSpecs

namespace MaxCutGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

variable {rows : Rows k}

def loaded (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineSourceTuple.stageTapes F tuple base k

def tupleBits (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) : List Bool :=
  (MachineOutcomeRows.selected rows (rhs F tuple)).flatMap (MachineOutcomeRows.payload B C values)

noncomputable def emitted (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineAddressEdge.appended (Slots k s d noiseCount) (loaded F tuple base)
    (tupleBits rows B C values F tuple)

noncomputable def finalTapes (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  AddressTupleCleanup.cleared k s d noiseCount (emitted rows B C values F tuple base)

structure Ready (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Prop where
  source : base .source = SourceEncoding.inputBits F
  saved : ∀j, base (.savedIndex j) = encodeWord (tuple j).val
  index : base .index = []
  work : base .work = []
  scratch : base .scratch = []
  copy : base .copyScratch = []
  fields : ∀j slot, base (.field j slot) = []

noncomputable def budget (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Nat :=
  (k * (10 * (SourceEncoding.inputBits F).length + 20) + 1) + 1 +
    ((MachineOutcomeRows.rowCosts (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)).sum + 1) +
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) + 1

theorem rhs_eq_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) :
    rhs F tuple = AddressOutcomeSpecs.rhsBits (source F) tuple := rfl

theorem canonicalValues_eq_actual (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) :
    AddressTupleLoaded.canonicalValues F tuple =
      CanonicalBodyTemplate.sourceFields tuple (ActualGame.names (source F)) := by
  funext j
  apply congrArg (fun names => CanonicalBodyTemplate.recordFields names (tuple j).val)
  funext slot
  fin_cases slot <;> rfl

theorem tupleBits_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) :
    tupleBits (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple =
      AddressOutcomeSpecs.tupleBits (source F) k T tuple := by
  unfold tupleBits
  rw [rhs_eq_actual, canonicalValues_eq_actual]
  exact AddressOutcomeSpecs.tuplePayload_actual (source F) k T tuple

/-- All generic template-correctness obligations are discharged from the
actual loader's canonical field values and the checked fixed-row specs. -/
theorem actualInvariant (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) (base : Arena k s d noiseCount → List Bool)
    (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base) := by
  constructor
  · exact AddressTupleLoaded.loaded_clean F tuple base clean
  · exact AddressTupleLoaded.loaded_radix F tuple base B hB
  · exact AddressTupleLoaded.loaded_capacity F tuple base C hC
  · intro spec member
    have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
    change (fun i => loaded F tuple base (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))) = _ at fields
    rw [fields]
    exact AddressOutcomeSpecs.correct_rows T (AddressTupleLoaded.canonicalValues F tuple)
      (rhs F tuple) spec member

theorem finalTapes_eq (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    finalTapes rows B C values F tuple base = MachineAddressEdge.appended
      (Slots k s d noiseCount) base (tupleBits rows B C values F tuple) :=
  AddressTupleFrame.cleared_appended_loaded F tuple base ready.index ready.work ready.fields _

end MaxCutGames.Integration.AddressTupleBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressOdometerSchedule
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressOdometerSchedule

open Turing
open MaxCutGames.Foundations.Complexity MachineTupleOdometer
open MaxCutGames.Foundations.Hastad
open MachineTransfer

noncomputable section

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def currentAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then current k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

def remainingAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then remaining k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

theorem setDigits_setAcc (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc base bits) = setAcc (setDigits m digits base) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [setDigits_other m digits _ tape hc hr, setAcc, ha]

theorem putDigit_setAcc (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (bits : List Bool) :
    putDigit j (setAcc base bits) a r = setAcc (putDigit j base a r) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [putDigit_other j _ a r tape (hc j) (hr j), setAcc, ha]

theorem setDigits_putDigit (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a r := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro tape hc hr
    simp [setDigits_other m digits _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m (Fin.snoc digits a) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a (m - 1 - a) := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro tape hc hr
    simp [setDigits_other m _ _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc_base (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a (m - 1 - a)) =
      setDigits m (Fin.snoc digits a) base := by
  rw [setDigits_putDigit, setDigits_snoc]

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ)
    {q : ℕ} (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (digit : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c digit i).val) =
      Fin.snoc (fun i => (c i).val) digit.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ k)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (accumulator k s d noiseCount))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt k s d noiseCount)
      (remaining := remainingAt k s d noiseCount) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    dsimp only [tree]
    erw [NestedCycle.LeafBound]
    exact hcount
  | succ q ih =>
    have hqu : q < k := by omega
    let schedule : CycleSchedule (Tape k s d noiseCount) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (accumulator k s d noiseCount))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
            (checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base), tree.LeafBound B := by
      let digit : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c digit)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (accumulator k s d noiseCount)))
        digit.val (m - 1 - digit.val)
      have hrem : m - 1 - digit.val = r.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = digit.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = digit.val + 1 := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, digit.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c digit) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical childBase childBits =
          checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
            schedule.ambient schedule.register schedule.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_accumulator, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) schedule children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, schedule,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        finalConfiguration (next (q + 1)) canonical base bits := by
      simp only [cycleExit, finalConfiguration, configuration, schedule, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
        (cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

/-- The time bound is derived from the concrete schedule, not from the number
of tuples alone. Dimension zero consists of its single actual body trace. -/
theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B : ℕ) (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin k → Fin m) → List Bool)
    (atCheck : ∀ i, i < k → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < k → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) k bodyLabel canonical base)
      (some (finalConfiguration (next k) canonical base bits))
      ((B + 2 * k) * m ^ k)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical
    positive B k (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

end
end MaxCutGames.Reduction.AddressOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OccurrenceTupleOrder
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-order bridge from the checked tuple odometer to the
outer reduction's occurrence enumeration. The odometer changes coordinate zero
fastest; `ActualEnumeration.functions` changes it slowest. Reading saved digit
`j.rev` as query coordinate `j` matches the complete ordered list. No primitive
machine or assumed whole-loop runtime is introduced here. -/

namespace MaxCutGames.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody

variable {k s d noiseCount : Nat}

theorem radix_le (F : SourceEncoding.Input) (s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      radixBound s d (SourceEncoding.inputBits F).length := by
  have h := source_counts_le F
  simp only [CanonicalAddress.base_eq, radixBound]
  omega

theorem radix_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := radix_le F s d
  unfold magnitude
  omega

theorem capacity_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    AddressGame.bodyCapacity (source F) k s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := Nat.pow_le_pow_left (radix_le F s d) (1+9*k)
  change (CanonicalAddress.base F.«variables» F.equations.length s d)^(1+9*k) ≤ _
  unfold magnitude
  omega

theorem canonicalValues_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    AddressTupleLoaded.canonicalValues F tuple j slot ≤
      (SourceEncoding.inputBits F).length := by
  rw [canonicalValues_eq_actual]
  unfold CanonicalBodyTemplate.sourceFields CanonicalBodyTemplate.recordFields
  split_ifs with h
  · have hname := (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).isLt
    have hvars := SourceEncoding.inputBits_length_ge_variables F
    change _ < F.«variables» at hname
    change (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).val ≤
      (SourceEncoding.inputBits F).length
    exact (Nat.le_of_lt hname).trans hvars
  · have hocc := (tuple j).isLt
    have hcount := SourceEncoding.inputBits_length_ge_equations F
    omega

theorem loaded_fields_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (i : Fin (4*k)) :
    ((loaded F tuple base) (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
  have atField := congrFun fields i
  change loaded F tuple base (MachineAddressEdge.addressSlots
    (Slots k s d noiseCount) (.field i)) = _ at atField
  rw [atField]
  simp only [CanonicalBodyMachine.savedFields, encodeWord_length]
  exact (Nat.add_le_add_right (canonicalValues_le F tuple _ _) 1).trans
    (field_length_le_magnitude k s d _)

/-- These are the actual canonical words, not arbitrary interpreted templates. -/
theorem queryWords_lt_radix (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (w : Nat) (hw : w ∈ AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) :
    w < CanonicalAddress.base F.«variables» F.equations.length s d := by
  rw [canonicalValues_eq_actual, rhs_eq_actual] at hw
  erw [AddressOutcomeSpecs.bitVector_rhsBits] at hw
  erw [AddressByteSemantics.queryWords_actual (source F) (tuple,X)] at hw
  exact CanonicalAddress.bodyWords_lt_base _ w hw

theorem queryWords_encoded_length_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d) :
    (encodeWords (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hwords := encodeWords_length_le
    (AddressByteSemantics.queryWords (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))
    (radixBound s d (SourceEncoding.inputBits F).length)
    (fun w hw => (Nat.le_of_lt (queryWords_lt_radix F tuple X w hw)).trans (radix_le F s d))
  rw [AddressByteSemantics.queryWords_length] at hwords
  unfold magnitude
  omega

theorem queryWords_digits_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (i : Nat) (hi : i < 1+9*k) :
    MachineTemplateAddress.digits (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) i ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hi' : i < (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))).length := by
    simpa only [AddressByteSemantics.queryWords_length] using hi
  simp only [MachineTemplateAddress.digits, List.getElem?_eq_getElem hi', Option.getD_some]
  exact (Nat.le_of_lt (queryWords_lt_radix F tuple X _ (List.getElem_mem hi'))).trans
    (radix_le_magnitude F k s d)

theorem selected_values_bound (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d) :
    ∀ row ∈ MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple),
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) := by
  rw [AddressOutcomeSpecs.selected_rows]
  intro row member
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
  simp only [AddressOutcomeSpecs.values_row_left, AddressOutcomeSpecs.values_row_right]
  exact ⟨queryWords_encoded_length_le_magnitude F tuple p.1,
    queryWords_encoded_length_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p),
    queryWords_digits_le_magnitude F tuple p.1,
    queryWords_digits_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p)⟩

theorem physicalField_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ≤
      (SourceEncoding.inputBits F).length := by
  have hv := SourceEncoding.inputBits_length_ge_variables F
  have hl := SourceEncoding.inputBits_length F
  have h₁ := F.equations[(tuple j).val].first.isLt
  have h₂ := F.equations[(tuple j).val].second.isLt
  have h₃ := F.equations[(tuple j).val].third.isLt
  fin_cases slot <;>
    simp only [SourceEncoding.equationWords, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> (try split_ifs) <;> omega

/-- Cleanup sees only the four loaded fields per position; output is not scanned. -/
theorem cleanup_budget_le (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) ≤
      4*k*((SourceEncoding.inputBits F).length+2) := by
  have h := lengthSum_le_of_mem_inline_AddressTupleBudget (AddressTupleCleanup.loadedFields k s d noiseCount)
    (emitted rows B C values F tuple base) ((SourceEncoding.inputBits F).length+1) (by
      intro tape member
      obtain ⟨j, slot, rfl⟩ :=
        (AddressTupleCleanup.mem_loadedFields k s d noiseCount tape).mp member
      rw [emitted, MachineAddressEdge.appended_other]
      · rw [loaded, AddressTupleLoaded.loaded_field F tuple base ready.fields, encodeWord_length]
        exact Nat.add_le_add_right (physicalField_le F tuple j slot) 1
      · rw [AddressMachineSpace.addressSlots_output]
        simp [AddressMachineSpace.headerTape])
  rw [AddressTupleCleanup.loadedFields_length] at h
  change MachineDrainMany.lengthSum _ _ + 4*k ≤ _
  calc
    _ ≤ 4*k*((SourceEncoding.inputBits F).length+1)+4*k := Nat.add_le_add_right h _
    _ = 4*k*((SourceEncoding.inputBits F).length+2) := by ring

end MaxCutGames.Integration.AddressTupleBudget

/-!
# Polynomial encoded length of the actual output

The encoder uses a unary, delimited forward-permutation
format. The instance is the actual list-based reduction, including canonical
body deduplication and every repeated edge occurrence. The polynomial's
coefficients depend only on the fixed gadget table and tuple dimensions.

These are output-length theorems. They do not assert a machine running-time
certificate for canonicalization, enumeration, or serialization.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Product
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The independent graph product in the last step of the v2 reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace MaxCutGames.Explicit.ProductPaddedOutput

open MaxCutGames.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (i : Fin (render G vertices edges hM).constraints.length) :
    (render G vertices edges hM).constraints[i] =
      row G vertices edges ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (side : Fin N → Bool)
    (leftSide : ∀ x, side (vertices (Sum.inl x)) = false)
    (rightSide : ∀ y, side (vertices (Sum.inr y)) = true) :
    SimpleBipartite (render G vertices edges hM) where
  side := side
  sourceSide i := by simp only [render_get, row, leftSide]
  targetSide i := by simp only [render_get, row, rightSide]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges ⟨i.val, hi⟩).source,
          (row G vertices edges ⟨i.val, hi⟩).target) =
        ((row G vertices edges ⟨j.val, hj⟩).source,
          (row G vertices edges ⟨j.val, hj⟩).target) := by
      simpa only [render_get] using! hij
    have he : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective he))

variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in
theorem count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  change countSatisfied labeling (List.ofFn (row G vertices edges)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, fullTable]

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_left [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (x : L) :
    extendLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  exact vertices.injective.extend_apply _ _ _

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_right [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (y : R) :
    extendLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  exact vertices.injective.extend_apply _ _ _

theorem maxSatisfied [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges hM) = G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    erw [count]
    exact G.satisfiedCount_le_maxSatisfied _ _
  · obtain ⟨left, right, hmax⟩ := G.maxSatisfied_attained
    have hcount := count G vertices edges hM (extendLabelings vertices left right)
    simp only [extendLabelings_left, extendLabelings_right, hmax] at hcount
    rw [← hcount]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges hM) (extendLabelings vertices left right)

theorem value [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.value (render G vertices edges hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [maxSatisfied, render_length]
  have hc : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hc]

end Embedded

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

local instance instNonemptyFinLengthConstraintVerticesConstraints : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩

def side (t : ℕ) (ht : 0 < t) (v : Fin (H.vertices ^ t)) : Bool :=
  presentation.side (finFunctionFinEquiv.symm v ⟨0, ht⟩)

end MaxCutGames.Explicit.ProductPaddedOutput

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

theorem initList_eq (bits : List Bool) : initList (machine k T) bits =
    ⟨some (start k T),AddressMachineSpace.initialState k,inputTapes k T bits⟩ := by
  change (⟨some (start k T),AddressMachineSpace.initialState k,
    (initList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (start k T),AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  funext tape
  by_cases h : tape = .source
  · subst tape; simp [initList,machine,inputTapes]; rfl
  · simp [initList,machine,inputTapes]
    erw [dite_eq_right h, Function.update_of_ne h]

end
end MaxCutGames.Reduction.AddressMachineProgram

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSingleOrbitProgram
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Physical postprocessing of the two-side address codec. The program reads
`2*C,q,m`, writes `C,q,m`, and replaces each row `u,C+v,table` by `u,v,table`.
Only the fixed alphabet size `q` occurs in finite control. All input-dependent
integers reside on unary tapes. Six Bool tapes suffice.
-/

namespace MaxCutGames.Explicit.MachineSingleOrbitProgram

open Turing
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction

def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .start => .push .capacity (fun _ => false)
      (.push .remaining (fun _ => false) (.goto fun _ => .halfFirst))
  | .halfFirst => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => .halfSecond)
        (.push .accumulator (fun _ => false)
          (.load (fun _ => initialState) (.goto fun _ => .alphabet))))
  | .halfSecond => .pop .input (fun state _ => state)
      (.push .capacity (fun _ => true)
        (.push .accumulator (fun _ => true) (.goto fun _ => .halfFirst)))
  | .alphabet => copyField .alphabet .count
  | .count => .pop .input (fun state head => (state.1, head))
      (.push .accumulator (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.push .remaining (fun _ => true) (.goto fun _ => .count))
          (.load (fun _ => initialState) (.goto fun _ => .guard))))
  | .guard => MachineUnaryCounter.guard .remaining .source .finishStart
  | .source => copyField .source .subtract
  | .subtract => .peek .capacity (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop .capacity (fun state _ => state)
          (.pop .input (fun state _ => state)
            (.push .saved (fun _ => true) (.goto fun _ => .subtract))))
        (.load (fun _ => initialState) (.goto fun _ => .restore)))
  | .restore => MachineTransfer.loopAt .saved .capacity id false .restore (some .target)
  | .target => copyField .target (.table 0)
  | .table completed =>
      if h : completed.val < q then
        copyField (.table completed) (.table ⟨completed.val + 1, by omega⟩)
      else .load (fun _ => initialState) (.goto fun _ => .guard)
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      () Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .start
  σ := State
  initialState := initialState
  m := program q

end MaxCutGames.Explicit.MachineSingleOrbitProgram

/-! Exact streaming traces in the single-orbit postprocessor. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitStreams

open Turing MaxCutGames.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram

theorem copyStep_true {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (true :: i) c s r a o) =
      some (cfg loopLabel (some true) i c s r (true :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg]

theorem copyStep_false {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (false :: i) c s r a o) =
      some (cfg exitLabel none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg, initialState]

/-- The physical field copy takes one transition for each input bit. -/
theorem copyFieldTrace {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (n : Nat) (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg loopLabel register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg exitLabel none suffix c s r ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing a register with
  | zero =>
    simpa [encodeWord] using copyStep_false loopLabel exitLabel atLoop suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some,
      copyStep_true loopLabel exitLabel atLoop, ih]
    congr 2
    simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

/-- All permutation fields are copied with a finite delimiter counter. -/
theorem tableTrace {q : Nat} (completed : Fin (q + 1)) (words : List Nat)
    (hcount : completed.val + words.length = q)
    (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some (cfg (.table completed) register (encodeWords words ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s r ((encodeWords words).reverse ++ a) o) := by
  induction words generalizing completed a register with
  | nil =>
    have hc : ¬ completed.val < q := by simp only [List.length_nil] at hcount; omega
    change some (TM2.stepAux (program q (.table completed)) _ _) = _
    simp [program, hc, TM2.stepAux, cfg, initialState, encodeWords]
  | cons n words ih =>
    have hc : completed.val < q := by simp only [List.length_cons] at hcount; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at hcount
      dsimp [next]
      omega
    have hp : program q (.table completed) = copyField (.table completed) (.table next) := by
      simp [program, hc, next]
    have first := copyFieldTrace (.table completed) (.table next) hp n
      (encodeWords words ++ suffix) c s r a o register
    have rest := ih next hn ((encodeWord n).reverse ++ a) none
    have ht : (encodeWords (n :: words)).length + 1 =
        ((encodeWords words).length + 1) + (n + 1) := by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega
    rw [ht, Function.iterate_add_apply]
    simp only [encodeWords, List.append_assoc]
    rw [first, rest]
    simp only [List.reverse_append, List.append_assoc]

end MaxCutGames.Explicit.MachineSingleOrbitStreams

/-! Physical unary header conversion, with an exact TM2 transition count. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitHeader

open Turing MaxCutGames.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem halfStep_first {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (true :: i) c s r a o) =
      some (cfg .halfSecond (some true) i c s r a o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_second {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfSecond register (true :: i) c s r a o) =
      some (cfg .halfFirst register i (true :: c) s r (true :: a) o) := by
  change some (TM2.stepAux (program q .halfSecond) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (false :: i) c s r a o) =
      some (cfg .alphabet none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

/-- Consume two unary input marks per output mark, storing the new capacity. -/
theorem halfTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * n + 1]
      (some (cfg .halfFirst register (encodeWord (2 * n) ++ suffix) c s r a o)) =
      some (cfg .alphabet none suffix (List.replicate n true ++ c) s r
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing c a register with
  | zero =>
    simpa [encodeWord] using halfStep_false suffix c s r a o register
  | succ n ih =>
    have ht : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
    have hw : encodeWord (2 * (n + 1)) ++ suffix =
        true :: true :: (encodeWord (2 * n) ++ suffix) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, ht, Function.iterate_succ_apply, advance_some, halfStep_first,
      Function.iterate_succ_apply, advance_some, halfStep_second, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem countStep_true {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (true :: i) c s r a o) =
      some (cfg .count (some true) i c s (true :: r) (true :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem countStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (false :: i) c s r a o) =
      some (cfg .guard none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

/-- Copy the occurrence count while also storing its physical unary counter. -/
theorem countTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .count register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s (List.replicate n true ++ r)
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing r a register with
  | zero =>
    simpa [encodeWord] using countStep_false suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some, countStep_true, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem initial_configuration (q : Nat) (input : List Bool) :
    initList (machine q) input = cfg .start none input [] [] [] [] [] := by
  have ht : (initList (machine q) input).stk = tapes input [] [] [] [] [] := by
    funext t
    cases t <;> simp [initList, machine, tapes]; rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem initialStep (q : Nat) (input : List Bool) :
    TM2.step (program q) (initList (machine q) input) =
      some (cfg .halfFirst none input [false] [] [false] [] []) := by
  rw [initial_configuration]
  change some (TM2.stepAux (program q .start) _ _) = _
  simp [program, TM2.stepAux, cfg]

/-- Read `2*C,q,m`, write `C,q,m`, and leave the physical unary capacity and
occurrence counters ready for the row loop.  The bound counts real transitions. -/
theorem headerTrace (q C m : Nat) (suffix : List Bool) :
    (advance (TM2.step (program q)))^[2 * C + q + m + 4]
      (some (initList (machine q)
        (encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix))) =
      some (cfg .guard none suffix (encodeWord C) [] (encodeWord m)
        (encodeWords [C, q, m]).reverse []) := by
  let input := encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix
  have hfirst :
      (advance (TM2.step (program q)))^[(2 * C + 1) + 1]
        (some (initList (machine q) input)) =
        some (cfg .alphabet none (encodeWord q ++ encodeWord m ++ suffix)
          (encodeWord C) [] [false] (encodeWord C).reverse []) := by
    rw [Function.iterate_add_apply _ (2 * C + 1) 1, Function.iterate_one]
    change (advance (TM2.step (program q)))^[2 * C + 1]
      (TM2.step (program q) (initList (machine q) input)) = _
    erw [initialStep q input]
    simpa only [input, encodeWord, List.append_nil, List.append_assoc] using
      halfTrace (q := q) C (encodeWord q ++ encodeWord m ++ suffix)
        [false] [] [false] [] [] none
  have hsecond :
      (advance (TM2.step (program q)))^[(q + 1) + ((2 * C + 1) + 1)]
        (some (initList (machine q) input)) =
        some (cfg .count none (encodeWord m ++ suffix) (encodeWord C) [] [false]
          ((encodeWord q).reverse ++ (encodeWord C).reverse) []) := by
    rw [Function.iterate_add_apply _ (q + 1) ((2 * C + 1) + 1), hfirst]
    simpa only [List.append_assoc] using
      copyFieldTrace (q := q) .alphabet .count rfl q (encodeWord m ++ suffix)
        (encodeWord C) [] [false] (encodeWord C).reverse [] none
  have ht : 2 * C + q + m + 4 = (m + 1) + ((q + 1) + ((2 * C + 1) + 1)) := by omega
  change (advance (TM2.step (program q)))^[2 * C + q + m + 4]
    (some (initList (machine q) input)) = _
  rw [ht, Function.iterate_add_apply _ (m + 1) ((q + 1) + ((2 * C + 1) + 1)), hsecond]
  have hlast := countTrace (q := q) m suffix (encodeWord C) [] [false]
    ((encodeWord q).reverse ++ (encodeWord C).reverse) [] none
  simpa [encodeWord, encodeWords, List.reverse_append, List.append_assoc] using hlast

end MaxCutGames.Explicit.MachineSingleOrbitHeader

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitSubtract

open Turing MaxCutGames.Foundations.Complexity MaxCutGames.Reduction
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem subtractStep_zero (q : Nat) (suffix saved remaining accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register suffix (encodeWord 0) saved remaining accumulator output) =
      some (cfg .restore none suffix (encodeWord 0) saved remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, initialState]

theorem subtractStep_succ (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register (List.replicate (n + 1) true ++ suffix)
        (encodeWord (n + 1)) saved remaining accumulator output) =
      some (cfg .subtract (some true) (List.replicate n true ++ suffix)
        (encodeWord n) (true :: saved) remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

/-- The scan consumes precisely the capacity prefix of the target field. -/
theorem subtractTrace (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .subtract register (List.replicate n true ++ suffix)
        (encodeWord n) saved remaining accumulator output)) =
      some (cfg .restore none suffix (encodeWord 0)
        (List.replicate n true ++ saved) remaining accumulator output) := by
  induction n generalizing saved register with
  | zero =>
    simpa using subtractStep_zero q suffix saved remaining accumulator output register
  | succ n ih =>
    rw [Function.iterate_succ_apply, advance_some, subtractStep_succ, ih]
    congr 2
    simp [List.replicate_add, List.append_assoc]

/-- The real saved-prefix transfer restores `C`, empties scratch, and takes
`C + 1` transitions. -/
theorem restoreTrace (q n : Nat) (suffix remaining accumulator output : List Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .restore none suffix (encodeWord 0) (List.replicate n true)
        remaining accumulator output)) =
      some (cfg .target none suffix (encodeWord n) [] remaining accumulator output) := by
  have h := MachineTransfer.transferAt_fromTapes (Γ := fun _ : Tape => Bool) (σ := Unit)
    Tape.saved Tape.capacity (by decide) id false (Label.restore : Label q) (some .target)
    (program q) rfl (tapes suffix (encodeWord 0) (List.replicate n true)
      remaining accumulator output) () none
  have next_eq : MachineTransfer.nextAt Tape.capacity (program q) =
      advance (TM2.step (program q)) := rfl
  rw [next_eq] at h
  simpa only [cfg, restore_tapes,
    tapes_saved, tapes_capacity, List.length_replicate,
    List.reverse_replicate, List.map_id, encodeWord, List.replicate_zero,
    List.nil_append] using h

/-- The complete target-offset removal preserves every other tape. In
particular the capacity is reusable and the `v` field delimiter is untouched. -/
theorem removeOffsetTrace (q C v : Nat) (suffix remaining accumulator output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * (C + 1)]
      (some (cfg .subtract register (encodeWord (C + v) ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .target none (encodeWord v ++ suffix) (encodeWord C)
        [] remaining accumulator output) := by
  have hw : encodeWord (C + v) ++ suffix =
      List.replicate C true ++ (encodeWord v ++ suffix) := by
    simp only [encodeWord, List.replicate_add, List.append_assoc]
  rw [hw, show 2 * (C + 1) = (C + 1) + (C + 1) by omega,
    Function.iterate_add_apply, subtractTrace]
  simp only [List.append_nil]
  exact restoreTrace q C (encodeWord v ++ suffix) remaining accumulator output

end MaxCutGames.Explicit.MachineSingleOrbitSubtract

/-! The exact input/output codec of the one-orbit postprocessor. Doubling is
only an encoding adapter: no equality of game values under independent labels
on the two copies is asserted. -/

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitFinish

open Turing MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

noncomputable section

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩) 1 where
  steps := 1
  evals_in_steps := by rfl
  steps_le_m := Nat.le_refl _

def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

end

end MaxCutGames.Explicit.MachineSingleOrbitFinish

/-!
Complete finite-machine postprocessing of the doubled address representation.
Every input field and row is physically processed. The time polynomial is in
the literal input bit length, including the final reversal and all tape cleanup.
-/

namespace MaxCutGames.Explicit.MachineSingleOrbitRuntime

open Turing MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitCodec MachineSingleOrbitRows

noncomputable section

def finalTapes {q : Nat} (I : Instance q) : Tape → List Bool :=
  tapes [] (encodeWord I.vertices) [] (encodeWord 0) (gameBits I).reverse []

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSingleOrbitFinish.timePolynomial q prefixPolynomial

end

end MaxCutGames.Explicit.MachineSingleOrbitRuntime

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

theorem stateTapes_ready (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressTupleBody.Ready F (OccurrenceTupleOrder.readCoordinates digits)
      (stateTapes k T F digits output) := by
  constructor
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_source k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j
    exact stateTapes_savedIndex k T F digits output j
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_index k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_work k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_scratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_copyScratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j slot
    rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_field k T F j slot
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

theorem stateTapes_clean (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) := by
  constructor
  · constructor
    · exact stateTapes_private k T F digits output .reversed
    · exact stateTapes_private k T F digits output .forward
    · exact stateTapes_private k T F digits output .copyScratch
    · exact stateTapes_private k T F digits output .accA
    · exact stateTapes_private k T F digits output .accB
    · exact stateTapes_private k T F digits output .counter
    · exact stateTapes_private k T F digits output .hornerScratch
    · intro j; exact stateTapes_private k T F digits output (.digit j)
  · exact stateTapes_private k T F digits output .output

theorem stateTapes_base (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_base]
  congr 1
  simp [MachineAddressHeaders.radix, MachineAddressHeaders.baseConstant,
    CanonicalAddress.base_eq, Nat.add_assoc]

theorem stateTapes_capacity (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (AddressGame.bodyCapacity (AddressTupleBody.source F) k s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_capacity]
  congr 1
  change MachineAddressHeaders.capacity k s d F.«variables» F.equations.length =
    CanonicalAddress.capacity F.«variables» F.equations.length k s d
  simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
    MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
    CanonicalAddress.base_eq, Nat.add_assoc]

/-- Appending actual tuple bytes is exactly the schedule's accumulator update. -/
theorem appended_stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output payload : List Bool) :
    MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) payload =
      stateTapes k T F digits (payload.reverse ++ output) := by
  change AddressOdometerSchedule.setAcc (stateTapes k T F digits output)
    (payload.reverse ++ stateTapes k T F digits output
      (AddressOdometerSchedule.accumulator k s d T.vectors.length)) = _
  simp only [stateTapes, AddressOdometerSchedule.setDigits_accumulator, AddressOdometerSchedule.setAcc_apply]
  rw [AddressOdometerSchedule.setDigits_setAcc, AddressOdometerSchedule.setAcc_setAcc,
    ← AddressOdometerSchedule.setDigits_setAcc]

/-- The all-zero assignment is already physically present after initialization. -/
theorem setDigits_initialized_zero (F : SourceEncoding.Input) :
    AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
      (AddressMachineInitial.initialized k T F) = AddressMachineInitial.initialized k T F := by
  funext tape
  cases tape with
  | savedIndex j =>
    rw [AddressOdometerSchedule.setDigits_savedIndex, AddressMachineInitial.initialized_savedIndex]
  | extra e =>
    rcases e with e | e
    · rfl
    · rcases e with e | e
      · rfl
      · rcases e with j | e
        · change AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
            (AddressMachineInitial.initialized k T F) (AddressOdometerSchedule.remaining k s d T.vectors.length j) = _
          simp only [AddressOdometerSchedule.setDigits_remaining, Fin.isLt, dite_eq_left, Nat.sub_zero]
          exact (AddressMachineInitial.initialized_remaining k T F j).symm
        · rfl
  | _ => rfl

end
end MaxCutGames.Reduction.AddressMachineLoop

/-!
The actual address machine's final bridge, cleanup, reversal, and halt. The
polynomial cleanup bound follows from space used by the supplied actual prefix
execution. The complete reduction supplies that prefix in `MachineAddressGame`.
-/

/-!
# The complete addressed outer-reduction machine

The fixed finite machine reads an encoded nonempty E3LIN occurrence list and
writes the exact encoded addressed Unique Games instance. Its execution covers
all headers, all occurrence tuples, every fixed noise/coefficient outcome,
every permutation image, reversal, and complete tape cleanup.
-/

/-!
The old addressed producer is reused only as a code generator. Its exact output
is the doubled codec of the new single-orbit game. The proved physical
postprocessor then yields the new game, with no premise about the value of the
legacy game and no legacy gadget or inverse theorem used.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

def main : Label := .inr .init

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionEmission
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal output-header emission and the initial occurrence-loop frame. -/

namespace MaxCutGames.Explicit.MachineSubdivisionEmission

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def headerInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, MachineSubdivisionInit.resultTapes n q Q body⟩
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (3 * (n + 7 * Q + 2) + 10) := by
  have run := MachineFieldTemplate.phaseInTime (headerTokens q) newHeaderField
    Tape.copyScratch Tape.accumulator
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide) (by decide)
    (Label.emitHeader : MachineFieldTemplate.Label (headerTokens q).length → Label q)
    (some .guard) (program q) (fun _ => rfl)
    (MachineSubdivisionInit.resultTapes n q Q body) rfl initialState
  rw [header_template, header_copiedLength, header_result] at run
  simpa only [machine, FinTM2.step, FinTM2.Cfg, MachineFieldTemplate.reset, initialState,
    headerTokens, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    using! run

/-- From raw input headers to the running occurrence loop, including all finite
arithmetic phases and literal output-header emission. -/
def prepareInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6 + 9 * MachineSubdivisionInit.stageCost n Q +
        (3 * (n + 7 * Q + 2) + 10)) := by
  have h := MachineSubdivisionHeaders.headersInTime q n Q body
  have i := MachineSubdivisionInit.initializeInTime q n Q body
  have e := headerInTime q n Q body
  have hi := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h i
  have hie := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hi e
  exact {
    toEvalsTo := hie.toEvalsTo
    steps_le_m := by
      have bound := hie.steps_le_m
      omega }

end MaxCutGames.Explicit.MachineSubdivisionEmission

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionTableRead
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual execution of the subdivision controller's full-table reader.
The reader consumes exactly the fixed number of zero-delimited table entries,
retains the unread input suffix, and reverses the saved table into forward order.
No table entry is stored in finite control; only the number of delimiters is.
-/

namespace MaxCutGames.Explicit.MachineSubdivisionTableRead

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

theorem step_true (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (true :: input) reversed⟩ =
      some ⟨some (.readTable completed), (ambient, some true),
        tapes base input (true :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

theorem step_false (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (false :: input) reversed⟩ =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input (false :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

/-- One encoded entry consumes its final delimiter in the same transition that
increments the finite completed-entry counter. -/
theorem readWordTrace (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (value : Nat) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[value + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWord value ++ input) reversed⟩) =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input ((encodeWord value).reverse ++ reversed)⟩ := by
  induction value generalizing reversed register with
  | zero =>
    simpa [encodeWord, MachineComposition.advance] using
      step_false q completed valid base input reversed ambient register
  | succ value ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      MachineComposition.advance_some]
    rw [step_true q completed valid]
    have h := ih (true :: reversed) (some true)
    simpa only [encodeWord, List.reverse_cons, List.reverse_append,
      List.append_assoc, List.singleton_append] using h

/-- Read a suffix of the q-entry table, stopping before any following data. -/
theorem readWordsTrace (q : Nat) (words : List Nat) (completed : Fin (q + 1))
    (complete : completed.val + words.length = q) (base : Tape → List Bool)
    (suffix reversed : List Bool) (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWords words ++ suffix) reversed⟩) =
      some ⟨some .reverseTable, (ambient, none),
        tapes base suffix ((encodeWords words).reverse ++ reversed)⟩ := by
  induction words generalizing completed reversed register with
  | nil =>
    have hc : ¬ completed.val < q := by simpa using complete.ge
    simp [encodeWords, MachineComposition.advance, TM2.step, program, hc, TM2.stepAux]
  | cons value words ih =>
    have valid : completed.val < q := by simp only [List.length_cons] at complete; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at complete
      dsimp [next]
      omega
    have first := readWordTrace q completed valid base value (encodeWords words ++ suffix)
      reversed ambient register
    have second := ih next hn ((encodeWord value).reverse ++ reversed) none
    rw [encodeWords, List.length_append, encodeWord_length,
      show value + 1 + (encodeWords words).length + 1 =
        ((encodeWords words).length + 1) + (value + 1) by omega,
      Function.iterate_add_apply]
    simp only [List.append_assoc]
    rw [first]
    simpa only [next, List.reverse_append, List.append_assoc] using second

/-- Full exact table phase: read q delimited entries and reverse the physical
saved stack, arriving at the actual row-emission label. -/
theorem tableTrace (q : Nat) (words : List Nat) (length : words.length = q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[2 * (encodeWords words).length + 2]
      (some ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords words ++ suffix) []⟩) =
      some ⟨some (rowEntry q), (ambient, none), finalTapes base suffix (encodeWords words)⟩ := by
  have read := readWordsTrace q words 0 (by simpa using length) base suffix [] ambient register
  simp only [List.append_nil] at read
  have reverse := MachineTransfer.transferAt_fromTapes
    Tape.permutationReverse Tape.permutation (by decide) id false
    Label.reverseTable (some (rowEntry q)) (program q) rfl
    (tapes base suffix (encodeWords words).reverse) ambient none
  have finish : MachineTransfer.tapesAt Tape.permutationReverse Tape.permutation
      (tapes base suffix (encodeWords words).reverse) []
      (((tapes base suffix (encodeWords words).reverse) .permutationReverse).reverse.map id ++
        (tapes base suffix (encodeWords words).reverse) .permutation) =
      finalTapes base suffix (encodeWords words) := by
    funext k
    cases k <;> simp [MachineTransfer.tapesAt, tapes, finalTapes]
  rw [finish] at reverse
  simp only [tapes_reverse, List.length_reverse] at reverse
  rw [show 2 * (encodeWords words).length + 2 =
      ((encodeWords words).length + 1) + ((encodeWords words).length + 1) by omega,
    Function.iterate_add_apply, read]
  exact reverse

/-- Timed witness for the actual controller, with a fixed alphabet-dependent
bound on its full forward table. Other row fields and unread input are preserved. -/
def tableInTime {q : Nat} (table : Target.PermutationTable q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords (tableWords table) ++ suffix) []⟩
      (some ⟨some (rowEntry q), (ambient, none),
        finalTapes base suffix (encodeWords (tableWords table))⟩)
      (2 * (q * (q + 1)) + 2) where
  steps := 2 * (encodeWords (tableWords table)).length + 2
  evals_in_steps := tableTrace q (tableWords table) (tableWords_length table)
    base suffix ambient register
  steps_le_m := by
    have h := GameEncodingSize.tableBits_length_le table
    omega

end MaxCutGames.Explicit.MachineSubdivisionTableRead

/-!
One whole occurrence iteration of the actual subdivision controller.
The proved trace includes both endpoint loads, the dynamic full-table reader,
the four-row template, all three local drains, and private-index increments.
-/

namespace MaxCutGames.Explicit.MachineSubdivisionBody

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def incrementInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .increment, initialState, base⟩
      (some ⟨some .guard, initialState, incrementTapes base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .increment) initialState base) = _
    simp [program, TM2.stepAux, incrementTapes, initialState]
  steps_le_m := Nat.le_refl _

/-- Complete actual `.startU → .guard` execution, without a phase-run premise. -/
def bodyInTime {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .startU, initialState, base⟩
      (some ⟨some .guard, initialState, bodyResult base u v table suffix⟩)
      (bodyBudget base u v table suffix) := by
  have hu : base .input = encodeWord u ++ (encodeWord v ++ tableBits table ++ suffix) := by
    simpa only [List.append_assoc] using ready.input
  let p₀ := SourceMachine.fieldInTime Tape.input Tape.u (by decide)
    Label.startU Label.readU (some .startV) (program q) rfl rfl base u
    (encodeWord v ++ tableBits table ++ suffix) hu ((), ()) none
  have hv : afterU base u v table suffix .input =
      encodeWord v ++ (tableBits table ++ suffix) := by
    simp [afterU, SourceMachine.afterField, SourceMachine.fieldTapes, List.append_assoc]
  let p₁ := SourceMachine.fieldInTime Tape.input Tape.v (by decide)
    Label.startV Label.readV (some (.readTable 0)) (program q) rfl rfl
    (afterU base u v table suffix) v (tableBits table ++ suffix) hv ((), ()) none
  have tableStart : MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
      (tableBits table ++ suffix) [] = afterV base u v table suffix := by
    funext k
    cases k <;> simp [MachineSubdivisionTableRead.tapes, afterV, afterU,
      SourceMachine.afterField, SourceMachine.fieldTapes, ready.reverseEmpty]
  have p₂ : StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), initialState, afterV base u v table suffix⟩
      (some ⟨some (rowEntry q), initialState, afterTable base u v table suffix⟩)
      (2 * (q * (q + 1)) + 2) := by
    have h := MachineSubdivisionTableRead.tableInTime table
      (afterV base u v table suffix) suffix ((), ()) none
    change StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨_, _, MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
        (tableBits table ++ suffix) []⟩ _ _ at h
    rw [tableStart] at h
    exact h
  have scratch : afterTable base u v table suffix .copyScratch = [] := by
    simp [afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
      afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, ready.scratchEmpty]
  let p₃ := MachineFieldTemplate.phaseInTime (rowTokens q) rowField
    Tape.copyScratch Tape.accumulator rowField_ne_scratch_inline_MachineSubdivisionBody rowField_ne_accumulator_inline_MachineSubdivisionBody (by decide)
    Label.emitRows (some .drainU) (program q) (fun _ => rfl)
    (afterTable base u v table suffix) scratch initialState
  let p₄ := MachineDrain.drainInTime Tape.u Label.drainU (some .drainV)
    (program q) rfl (afterRows base u v table suffix) ((), ()) none
  let p₅ := MachineDrain.drainInTime Tape.v Label.drainV (some .drainPermutation)
    (program q) rfl (afterDrainU base u v table suffix) ((), ()) none
  let p₆ := MachineDrain.drainInTime Tape.permutation Label.drainPermutation (some .increment)
    (program q) rfl (afterDrainV base u v table suffix) ((), ()) none
  let p₇ := incrementInTime q (afterDrainTable base u v table suffix)
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅
  let p₀₁₂₃₄₅₆ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆
  let full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅₆ p₇
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      have h := full.steps_le_m
      have tokens_length : (rowTokens q).length = 12 := rfl
      unfold bodyBudget
      omega
  }

end MaxCutGames.Explicit.MachineSubdivisionBody

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

namespace MaxCutGames.Explicit.MachineSubdivisionLoopFrame

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

theorem guard_cons {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    (machine q).step ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ =
      some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩ := by
  have before : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) (edges.length + 1) [] =
      frame Q e (edge :: edges) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e (edge :: edges) emitted) Tape.remaining
      ((frame Q e (edge :: edges) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have after : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) edges.length [] =
      afterGuard Q e edge edges emitted := by
    simp [MachineUnaryCounter.counterTapes, afterGuard]
  have run := MachineUnaryCounter.guardStep_succ Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e (edge :: edges) emitted) edges.length [] ((), ()) none
  rw [before, after] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

theorem guard_nil (n q Q e : Nat) (emitted : List Bool) :
    (machine q).step
      ⟨some .guard, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ =
      some ⟨some .finishStart, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ := by
  have framed : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e ([] : List (Constraint n q)) emitted) 0 [] =
      frame Q e ([] : List (Constraint n q)) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e ([] : List (Constraint n q)) emitted) Tape.remaining
      ((frame Q e ([] : List (Constraint n q)) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have run := MachineUnaryCounter.guardStep_zero Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e ([] : List (Constraint n q)) emitted) [] ((), ()) none
  rw [framed] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

end MaxCutGames.Explicit.MachineSubdivisionLoopFrame

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

/-! Complete physical occurrence traversal of the subdivision program. -/

namespace MaxCutGames.Explicit.MachineSubdivisionLoop

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame

def bodyInTime {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) (he : e ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩
      (some ⟨some .guard, initialState, frame Q (e + 1) edges (emitted ++ rowBits Q e edge)⟩)
      (bodyBound n q Q) := by
  have run := MachineSubdivisionBody.bodyInTime (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
  rw [bodyResult_eq_frame] at run
  have bound := MachineSubdivisionBodySpec.bodyBudget_le (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
    n Q e edge.source.isLt edge.target.isLt he rfl rfl rfl
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := run.steps_le_m.trans bound }

/-- Every list occurrence is read once, emits exactly its four rows, and advances
the three private numeric names. The loop includes its final zero-counter test. -/
def loopInTime {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) (fit : e + edges.length ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .guard, initialState, frame Q e edges emitted⟩
      (some ⟨some .finishStart, initialState,
        frame Q (e + edges.length) ([] : List (Constraint n q))
          (emitted ++ outputRows Q e edges)⟩)
      (edges.length * (bodyBound n q Q + 1) + 1) := by
  induction edges generalizing e emitted with
  | nil =>
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
    change (machine q).step ⟨some .guard, initialState, frame Q e [] emitted⟩ = _
    simpa only [List.length_nil, Nat.add_zero, outputRows, List.append_nil]
      using guard_nil n q Q e emitted
  | cons edge edges ih =>
    have he : e ≤ Q := by simp only [List.length_cons] at fit; omega
    have remainingFit : (e + 1) + edges.length ≤ Q := by
      simp only [List.length_cons] at fit
      omega
    have guard : StateTransition.EvalsToInTime (machine q).step
        ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩
        (some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩) 1 := {
      steps := 1
      evals_in_steps := by
        change (machine q).step
          ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ = _
        exact guard_cons Q e edge edges emitted
      steps_le_m := Nat.le_refl _ }
    have body := bodyInTime Q e edge edges emitted he
    have tail := ih (e + 1) (emitted ++ rowBits Q e edge) remainingFit
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first tail
    have index_eq : (e + 1) + edges.length = e + (edge :: edges).length := by simp; omega
    have words_eq : (emitted ++ rowBits Q e edge) ++ outputRows Q (e + 1) edges =
        emitted ++ outputRows Q e (edge :: edges) := by
      simp only [outputRows, List.append_assoc]
    rw [index_eq, words_eq] at whole
    exact {
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega }

end MaxCutGames.Explicit.MachineSubdivisionLoop

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

namespace MaxCutGames.Explicit.MachineSubdivisionFinish

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineSubdivisionProgram

noncomputable def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

theorem haltList_eq (q : Nat) (bits : List Bool) :
    haltList (machine q) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]
  rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .finishStart) initialState base) = _
    simp only [program, TM2.stepAux]
    rfl
  steps_le_m := Nat.le_refl _

end MaxCutGames.Explicit.MachineSubdivisionFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionCorrespondence
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual streamed bytes coincide with the numbered semantic subdivision.
The controller copies the last table unchanged, so its input contract explicitly
requires involutive tables; binary translations satisfy this condition. -/

namespace MaxCutGames.Explicit.MachineSubdivisionCorrespondence

open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionLoopFrame

def Involutive {q : Nat} (H : Instance q) : Prop :=
  ∀ e : Fin H.constraints.length,
    MachineSubdivisionRows.inverseTable H.constraints[e].permutation = H.constraints[e].permutation

theorem inverseTable_eq {q : Nat} (p : PermutationTable q)
    (same : p.inverseImages = p.images) : MachineSubdivisionRows.inverseTable p = p := by
  cases p with
  | mk images inverseImages left right =>
    dsimp at same
    cases same
    rfl

theorem translations_involutive {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (translations : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Involutive H := by
  intro e
  apply inverseTable_eq
  apply Vector.ext
  intro i hi
  apply coordinates.injective
  obtain ⟨shift, law⟩ := translations H.constraints[e] (List.getElem_mem e.isLt)
  have h := law (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)])
  rw [H.constraints[e].permutation.rightInverse] at h
  have cancel : shift + shift = 0 := by
    ext j
    simp [CharTwo.add_self_eq_zero]
  have doubled := congrArg (fun x => x + shift) h
  have inverseLaw : coordinates (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)]) =
      coordinates ⟨i, hi⟩ + shift := by
    simpa only [add_assoc, cancel, add_zero] using doubled.symm
  exact inverseLaw.trans (law ⟨i, hi⟩).symm

theorem rowBits_eq_semantic {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (involutive : Involutive H) :
    rowBits H.constraints.length e.val H.constraints[e] =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
  have words := MachineSubdivisionBodySpec.rowBits_eq_dynamic
    (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation
  have vertices (j : Fin 5) := SubdivisionTarget.vertexFields_val H e j
  simp only [MachineSubdivisionRows.subdivisionVertexWords] at vertices
  have dynamic : MachineSubdivisionDynamicRows.rowBits
      (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
    simp only [MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionRows.rowBits,
      MachineSubdivisionDynamicRows.rows, MachineSubdivisionRows.rows, involutive e]
  rw [← dynamic, ← words]
  simp only [vertices, MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem outputRows_eq_ofFn {n q : Nat} (Q e : Nat) (edges : List (Constraint n q)) :
    outputRows Q e edges =
      (List.ofFn (fun i : Fin edges.length => rowBits Q (e + i.val) edges[i])).flatten := by
  induction edges generalizing e with
  | nil => rfl
  | cons edge edges ih =>
    rw [outputRows, ih, List.ofFn_succ]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem outputRows_eq_semantic {q : Nat} (H : Instance q) (involutive : Involutive H) :
    outputRows H.constraints.length 0 H.constraints =
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
          H.constraints[e].permutation) := by
  rw [outputRows_eq_ofFn]
  simp only [Nat.zero_add, rowBits_eq_semantic H _ involutive, List.ofFn_eq_map,
    List.flatMap_def]

/-- Exact complete serialized output, including the changed headers and every
forward permutation-table entry, in occurrence order. -/
theorem output_eq_gameBits {q : Nat} (H : Instance q) (involutive : Involutive H) :
    MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints =
      gameBits (SubdivisionTarget.subdivide H) := by
  rw [SubdivisionEncoding.subdivide_gameBits, outputRows_eq_semantic H involutive]
  rfl

end MaxCutGames.Explicit.MachineSubdivisionCorrespondence

/-! The complete finite subdivision machine, including its polynomial runtime
in the actual serialized input length and exact full-table output. -/

namespace MaxCutGames.Explicit.MachineSubdivisionRuntime

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame
open MachineSubdivisionCorrespondence

noncomputable section

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSubdivisionFinish.timePolynomial q (prefixPolynomial q)

theorem input_eq {q : Nat} (H : Instance q) :
    gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++ bodyBits H.constraints := by
  simp only [gameBits, gameWords, bodyBits, encodeWords_append]

theorem input_size {q : Nat} (H : Instance q) :
    H.vertices ≤ (gameBits H).length ∧ H.constraints.length ≤ (gameBits H).length := by
  rw [input_eq]
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

def finalTapes {q : Nat} (H : Instance q) : Tape → List Bool :=
  frame H.constraints.length H.constraints.length ([] : List (Constraint H.vertices q))
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints)

theorem final_outputEmpty {q : Nat} (H : Instance q) : finalTapes H .output = [] := rfl

theorem final_accumulator {q : Nat} (H : Instance q) (involutive : Involutive H) :
    finalTapes H .accumulator = (gameBits (SubdivisionTarget.subdivide H)).reverse := by
  change (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
    outputRows H.constraints.length 0 H.constraints).reverse = _
  rw [output_eq_gameBits H involutive]

/-- The prefix contains every actual header read, fresh-name initialization,
header emission, complete four-row body, and occurrence-counter test. -/
def prefixInTime {q : Nat} (H : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits H))
      (some ⟨some .finishStart, initialState, finalTapes H⟩)
      ((prefixPolynomial q).eval (gameBits H).length) := by
  have initial := MachineSubdivisionEmission.prepareInTime q H.vertices H.constraints.length
    (bodyBits H.constraints)
  rw [← input_eq H, ← frame_prepared H.constraints] at initial
  have loop := MachineSubdivisionLoop.loopInTime H.constraints.length 0 H.constraints
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length) (by simp)
  simp only [Nat.zero_add] at loop
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := ?_ }
  have hn := (input_size H).1
  have hQ := (input_size H).2
  have bodyBound : MachineSubdivisionLoop.bodyBound H.vertices q H.constraints.length + 1 ≤
      100 * (4 * (gameBits H).length + q * (q + 1) + 1) + 1 := by
    unfold MachineSubdivisionLoop.bodyBound
    omega
  have loopBound := Nat.mul_le_mul hQ bodyBound
  have prepBound : H.vertices + q + H.constraints.length + 6 +
      9 * MachineSubdivisionInit.stageCost H.vertices H.constraints.length +
      (3 * (H.vertices + 7 * H.constraints.length + 2) + 10) ≤
      62 * (gameBits H).length + q + 49 := by
    unfold MachineSubdivisionInit.stageCost
    omega
  have bound := whole.steps_le_m
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  omega

end
end MaxCutGames.Explicit.MachineSubdivisionRuntime

namespace MaxCutGames.Explicit.MachineSubdivisionCompose

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionCorrespondence

noncomputable section

variable {α : Type} {q : Nat} {encode : α → List Bool} {f : α → Instance q}

def certifiedOutput (involutive : ∀ a, Involutive (f a)) (a : α) :
    {H : Instance q // Involutive H} := ⟨f a, involutive a⟩

/-- Attach the already-proved property without executing anything or changing
the input or output codec. -/
def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      (certifiedOutput involutive) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

end
end MaxCutGames.Explicit.MachineSubdivisionCompose

end OAI
end


