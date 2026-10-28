-- Prove2me | Definitions.Def_OAIQ087A029
-- name    : OAIQ087A029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:42:24.074129+00:00
-- url     : https://prove2.me/theorems/43161bb4-b982-4b95-874c-1f1d8252f3ae
-- title:
--   Definitions bundle OAIQ087A029 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 235 declarations of OpenAI's Lean: 97 definitions, 3 inductive types or structures and 135 theorems. The definitions and types are `OAI.MaxCutGames.Explicit.MachineSingleOrbitBridge.computableInPolyTime`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitBridge.doubledComputableInPolyTime`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitFinish.completePrefix`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRows.rowCost`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRows.rowsCost`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRuntime.computableInPolyTime`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRuntime.fullRunInTime`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRuntime.prefixCost`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRuntime.prefixInTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionCompose.computableInPolyTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionCompose.translationComputableInPolyTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionFinish.completePrefix`, `OAI.MaxCutGames.Explicit.MachineSubdivisionRuntime.computableInPolyTime`, `OAI.MaxCutGames.Explicit.MachineSubdivisionRuntime.fullRunInTime`, `OAI.MaxCutGames.Explicit.MachineUniformRun.computation`, `OAI.MaxCutGames.Explicit.MachineUniformRun.outputInTime`, `OAI.MaxCutGames.Explicit.ProductPaddedOutput.simpleBipartite`, `OAI.MaxCutGames.FinishReduction.of_matrix_reduction`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.Label`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.chosen`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.cleanupEntry`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.cleanupExecution`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.cleanupLabel`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.completedMachine`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.completedProgram`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.embeddedCfg`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.outputsInTime`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFCleanup.resetLabel`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.LoopInvariant`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.LoopRun`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.RawRun`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.computableInPolyTime`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.emitInTime`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.emittedBytes`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.endpointsInTime`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.finalTimePolynomial`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.finishInTime`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.formulaHeader`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.guardEndInTime`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.guardRowInTime` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Games_AddressGame`, `MaxCut_Games_AddressTupleLoaded`, `MaxCut_Games_FinalCNFHeader`, `MaxCut_Games_FinalCNFOutput`, `MaxCut_Games_FinalCNFStream`, `MaxCut_Games_GraphIterationBounds`, `MaxCut_Games_OccurrenceTupleOrder`, `MaxCut_Games_Product`, `MaxCut_Games_ProductSoundness`, `MaxCut_Machines_AddressMachineInitial`, `MaxCut_Machines_AddressMachineLoop`, `MaxCut_Machines_CloneMachineModel`, `MaxCut_Machines_GraphCounterFinish`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_Machine`, `MaxCut_Machines_MachineCanonicalOutput`, `MaxCut_Machines_MachineExpanderRowFrames`, `MaxCut_Machines_MachineExpanderTableRows`, `MaxCut_Machines_MachineLazyTable`, `MaxCut_Machines_MachineLazyTableRuntime`, `MaxCut_Machines_MachineRegularOriginalBody`, `MaxCut_Machines_MachineRegularTableRuntime`, `MaxCut_Machines_MachineRhsLoad`, `MaxCut_Machines_MachineSingleOrbitProgram`, `MaxCut_Machines_MachineSubdivisionCorrespondence`, `MaxCut_Machines_MachineSubdivisionTableRead`, `MaxCut_Machines_MachineTemplateAddress`, `MaxCut_Machines_RawInitialMachineCleanup`, `MaxCut_Machines_RuntimeSpace`, `MaxCut_PCP_HeaderCounts`.
--
--   **Imports.** It imports the bundles `OAIQ087A021`, `OAIQ087A022`, `OAIQ087A023` and `OAIQ087A024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A033` and `OAIQ087A034`; the proof of `OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A021
import Definitions.Def_OAIQ087A022
import Definitions.Def_OAIQ087A023
import Definitions.Def_OAIQ087A024

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Machine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complete-stack cleanup, with an arbitrary continuation. Each symbol
costs one transition and the empty-stack branch costs one final transition. -/

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- With a clean register, complete work-tape cleanup reaches the standard
halted shape, preserving the output word and the ambient state exactly. -/
theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end MaxCutGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderCounts
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

namespace Eval

open CookLevin.PolynomialMachine

variable {K Λ σ : Type} [DecidableEq K]

theorem trace (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement p slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl 0)) = encodeWord n)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p n]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
  have hp : (advance (TM2.step program))^[1]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (inner p .start)), ((ambient, ()), register), prepared p slots base⟩ := by
    change some (TM2.stepAux (program (labels (start p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (prependFields _ _ _) _ _) = _
    rw [stepAux_prependFields]
    rfl
  have hh := MachineHorner.hornerTrace slots (fun l => labels (inner p l))
    (some (labels (finish p))) program (fun l => atLabels (inner p l))
    (prepared p slots base) n (digit p) (by simpa using hinput)
    (fun i => prepared_digit p slots base i (hcoeff i))
    (by
      constructor
      · simpa using clean.accA
      · simpa using clean.accB
      · simpa using clean.counter
      · simpa using clean.scratch) ambient register
  rw [hornerValue_eq_eval] at hh
  have hc : (advance (TM2.step program))^[1]
      (some ⟨some (labels (finish p)), ((ambient, ()), none),
        MachineHorner.resultTapes slots (prepared p slots base) (p.eval n)⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
    change some (TM2.stepAux (program (labels (finish p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (clearFields _ _ _) _ _) = _
    rw [stepAux_clearFields, clear_result p slots base _ hcoeff]
    cases exit <;> rfl
  rw [show steps p n = 1 + (MachineHorner.steps n (digit p) (width p) + 1) by
    unfold steps; omega, Function.iterate_add_apply, Function.iterate_add_apply, hp, hh, hc]

end Eval

end

end MaxCutGames.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CloneMachineModel
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
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

namespace MaxCutGames.Reduction.CloneMachineAffine

open MaxCutGames.Foundations.Complexity
open CloneMachineModel

/-- This includes zero scale and zero offset, with no positivity assumptions. -/
theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

end MaxCutGames.Reduction.CloneMachineAffine

namespace MaxCutGames.Reduction.MachineAddressHeaders

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineComposition

noncomputable section

namespace Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem WorkClean.update_control {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : WorkClean slots base) (c : Control)
    (other : c ≠ .accA ∧ c ≠ .accB ∧ c ≠ .counter ∧ c ≠ .scratch) (word : List Bool) :
    WorkClean slots (Function.update base (control slots c) word) := by
  constructor
  · simpa [other.1.symm] using clean.accA
  · simpa [other.2.1.symm] using clean.accB
  · simpa [other.2.2.1.symm] using clean.counter
  · simpa [other.2.2.2.symm] using clean.scratch
  · intro i
    simpa [control, slots.injective.eq_iff] using clean.coefficients i

/-- One placed invocation of the already checked preserving polynomial evaluator. -/
theorem evalPhaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (kind : Kind) (base : K → List Bool) (value : Nat)
    (hinput : base (control slots (inputControl kind)) = encodeWord value)
    (hdest : base (control slots (outputControl kind)) = [])
    (clean : WorkClean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount kind) value]
      (some ⟨some (labels (evalStart kind)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (afterEval kind)), ((ambient, ()), none),
        Function.update base (control slots (outputControl kind))
          (encodeWord ((polynomial k s d noiseCount kind).eval value))⟩ := by
  have evaluated := SourceHeaderCounts.Eval.trace (polynomial k s d noiseCount kind)
    (evalSlots slots kind) (fun label => labels (.evaluate kind label))
    (some (labels (afterEval kind))) program (fun label => atLabels (.evaluate kind label))
    base value (by simpa using hinput)
    (fun i => by simpa using clean.coefficients (coefficientBlock k s d noiseCount kind i))
    ⟨by simpa using clean.accA, by simpa using clean.accB,
      by simpa using clean.counter, by simpa using clean.scratch⟩ ambient register
  simpa only [evalStart, MachineHorner.resultTapes, evalSlots_destination, hdest, List.append_nil]
    using evaluated

/-- Copies preserve both operands; addition consumes only the temporary copy. -/
theorem prepareBaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * n + 3 * m + 10]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none),
        preparedBase slots base n m⟩ := by
  let t1 := Function.update base (control slots .baseValue) (encodeWord n)
  let t2 := Function.update t1 (control slots .temporary) (encodeWord m)
  let t3 := Function.update (Function.update t2 (control slots .temporary) [false])
    (control slots .baseValue) (encodeWord (m + n))
  let t4 := Function.update (Function.update t3 (control slots .temporary) [])
    (control slots .baseValue) (encodeWord (radix s d n m))
  have copyingN := MachineCopy.copyTrace (control slots .variableCount)
    (control slots .baseValue) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyNOut) (labels .copyNBack) (some (labels .copyMOut)) program
    (atLabels .copyNOut) (atLabels .copyNBack) base clean.scratch (ambient, ()) register
  rw [hn, clean.baseValue, List.append_nil, encodeWord_length] at copyingN
  have copyingM := MachineCopy.copyTrace (control slots .occurrenceCount)
    (control slots .temporary) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyMOut) (labels .copyMBack) (some (labels .addM)) program
    (atLabels .copyMOut) (atLabels .copyMBack) t1
    (by simpa [t1] using clean.scratch) (ambient, ()) none
  have hm1 : t1 (control slots .occurrenceCount) = encodeWord m := by simpa [t1] using hm
  have ht1 : t1 (control slots .temporary) = [] := by simpa [t1] using clean.temporary
  rw [hm1, ht1, List.append_nil, encodeWord_length] at copyingM
  have adding := MachineUnaryAddAt.addFromTapes (control slots .temporary)
    (control slots .baseValue) (by simp) (labels .addM) (some (labels .seedBase)) program
    (atLabels .addM) t2 m n [] [] (by simp [t2]) (by simp [t2, t1]) (ambient, ()) none
  have added : MachineUnaryAddAt.unaryTapes (control slots .temporary)
      (control slots .baseValue) t2 0 (m + n) [] [] = t3 := by
    simp [MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, t3, encodeWord]
  rw [added] at adding
  have seeding : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedBase), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .seedBase)) _ _) = _
    rw [atLabels]
    simp only [statement, TM2.stepAux]
    have htemp : t3 (control slots .temporary) = [false] := by simp [t3]
    rw [htemp]
    simp only [List.tail_cons]
    rw [MachineSubstitution.stepAux_pushWord]
    simp only [TM2.stepAux]
    have different : control slots .baseValue ≠ control slots .temporary := by simp
    rw [Function.update_of_ne different]
    have hbase : t3 (control slots .baseValue) = encodeWord (m + n) := by simp [t3]
    rw [hbase]
    have wordEq : (List.replicate (baseConstant s d) true).reverse ++ encodeWord (m + n) =
        encodeWord (radix s d n m) := by
      simp [encodeWord, List.reverse_replicate, ← List.append_assoc,
        List.replicate_append_replicate, radix, Nat.add_comm, Nat.add_assoc]
    rw [wordEq]
  have combined := trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ copyingN copyingM) adding) seeding
  have timeEq : 2 * (n + 1 + 1) + 2 * (m + 1 + 1) + (m + 1) + 1 =
      2 * n + 3 * m + 10 := by omega
  rw [timeEq] at combined
  have frame : t4 = preparedBase slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [t4, t3, t2, t1, preparedBase, clean.temporary]
    · simp [t4, t3, t2, t1, preparedBase, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

/-- Physical doubling emits the vertex-count word and restores the capacity. -/
theorem doubleTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (value : Nat)
    (hcap : base (control slots .capacity) = encodeWord value)
    (hscratch : base (control slots .scratch) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[3 * value + 5]
      (some ⟨some (labels .doubleScan), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .alphabet), ((ambient, ()), none),
        Function.update base (control slots .reversed)
          ((encodeWord (2 * value)).reverse ++ base (control slots .reversed))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace (control slots .capacity)
    (control slots .scratch) (control slots .reversed) (by simp) (by simp) (by simp)
    () (fun q _ => q) (fun _ : Unit => CloneMachineModel.affineEmit 2 0)
    (labels .doubleScan) (labels .doubleRestore) (fun _ symbol => labels (.doubleEmit symbol))
    (some (labels .alphabet)) program (atLabels .doubleScan)
    (by intro q symbol; cases q; exact atLabels (.doubleEmit symbol))
    (atLabels .doubleRestore) base hscratch ambient () register
  rw [hcap, CloneMachineAffine.output_eq_flatMap, CloneMachineAffine.affineEmit_word,
    Nat.zero_add, encodeWord_length] at copied
  have timeEq : 3 * (value + 1) + 2 = 3 * value + 5 := by omega
  rw [timeEq] at copied
  exact copied

/-- All arithmetic and header emission, with exact composed transition count. -/
theorem trace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps k s d noiseCount n m]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := preparedBase slots base n m
  let t2 := Function.update t1 (control slots .capacity) (encodeWord (capacity k s d n m))
  let t3 := Function.update t2 (control slots .reversed)
    ((encodeWord (2 * capacity k s d n m)).reverse ++ t2 (control slots .reversed))
  let t4 := Function.update t3 (control slots .reversed)
    ((encodeWord (2 ^ s)).reverse ++ t3 (control slots .reversed))
  let t5 := Function.update t4 (control slots .temporary) (encodeWord (edgeCount k s d noiseCount m))
  have prepared := prepareBaseTrace slots labels exit program atLabels base n m hn hm clean ambient register
  have cw1 : WorkClean slots t1 := clean.toWorkClean.update_control .baseValue (by decide) _
  have evaluatedCap := evalPhaseTrace slots labels exit program atLabels .capacity t1 (radix s d n m)
    (by simp [t1, preparedBase, inputControl])
    (by simpa [t1, preparedBase, outputControl] using clean.capacity) cw1 ambient none
  simp only [polynomial_capacity_eval] at evaluatedCap
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .capacity) (radix s d n m)]
    (some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t1⟩) =
    some ⟨some (labels .doubleScan), ((ambient, ()), none), t2⟩ at evaluatedCap
  have cw2 : WorkClean slots t2 := cw1.update_control .capacity (by decide) _
  have doubled := doubleTrace slots labels exit program atLabels t2 (capacity k s d n m)
    (by simp [t2]) cw2.scratch ambient none
  have alphabetStep : (advance (TM2.step program))^[1]
      (some ⟨some (labels .alphabet), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .alphabet)) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (MachineSubstitution.pushWord _ _ _) _ _) = _
    rw [MachineSubstitution.stepAux_pushWord]
    rfl
  have cw3 : WorkClean slots t3 := cw2.update_control .reversed (by decide) _
  have cw4 : WorkClean slots t4 := cw3.update_control .reversed (by decide) _
  have evaluatedEdges := evalPhaseTrace slots labels exit program atLabels .edges t4 m
    (by simpa [t4, t3, t2, t1, preparedBase, inputControl] using hm)
    (by simpa [t4, t3, t2, t1, preparedBase, outputControl] using clean.temporary)
    cw4 ambient none
  simp only [polynomial_edges_eval] at evaluatedEdges
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .edges) m]
    (some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩) =
    some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩ at evaluatedEdges
  have transferred := MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
    (σ := σ × Unit) (control slots .temporary)
    (control slots .reversed) (by simp) id false (labels .edgeTransfer) exit program
    (atLabels .edgeTransfer) t5 (ambient, ()) none
  change (advance (TM2.step program))^[(t5 (control slots .temporary)).length + 1]
    (some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩) = _ at transferred
  have ht5 : t5 (control slots .temporary) = encodeWord (edgeCount k s d noiseCount m) := by simp [t5]
  rw [ht5, encodeWord_length] at transferred
  simp only [List.map_id] at transferred
  have combined := trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _
    (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ prepared evaluatedCap) doubled) alphabetStep) evaluatedEdges) transferred
  have timeEq : 2 * n + 3 * m + 10 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
      (3 * capacity k s d n m + 5) + 1 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
      (edgeCount k s d noiseCount m + 1 + 1) = steps k s d noiseCount n m := by
    unfold steps
    omega
  rw [timeEq] at combined
  have frame : MachineTransfer.tapesAt (control slots .temporary) (control slots .reversed)
      t5 [] ((encodeWord (edgeCount k s d noiseCount m)).reverse ++ t5 (control slots .reversed)) =
      resultTapes slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [MachineTransfer.tapesAt, resultTapes, clean.temporary]
    · simp [MachineTransfer.tapesAt, t5, t4, t3, t2, t1, preparedBase, resultTapes,
        headerBits, encodeWords, List.reverse_append, List.append_assoc, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

def inTime (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps k s d noiseCount n m) where
  steps := steps k s d noiseCount n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

end Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

theorem Clean.afterPrefix {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (n m : Nat) :
    Arithmetic.Clean (arithmeticSlots slots) (Prefix.resultTapes (prefixSlots slots) base n m) := by
  constructor
  · constructor
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accA
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accB
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.counter
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.scratch
    · intro i; rw [prefixResult_coefficient]; exact clean.coefficients i
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.baseValue
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.capacity
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.temporary

def inTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.«variables» input.equations.length⟩)
      (Arithmetic.steps k s d noiseCount input.«variables» input.equations.length +
        (3 * (SourceEncoding.inputBits input).length + 6)) := by
  have parsed := Prefix.inTime (prefixSlots slots) (fun l => labels (.inl l))
    (some (labels (.inr .copyNOut))) program (fun l => atLabels (.inl l))
    base input.«variables» input.equations.length
    (encodeWords (input.equations.flatMap SourceEncoding.equationWords))
    (by simpa [prefixSlots, prefixLocal_apply, SourceEncoding.inputBits,
      SourceEncoding.inputWords, encodeWords, List.append_assoc] using hinput)
    clean.readCopy clean.scratch ambient register
  have hn : Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .variableCount) = encodeWord input.«variables» := by
    change Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (prefixSlots slots 2) = _
    rw [Prefix.resultTapes_n]
    change encodeWord input.«variables» ++
      base (Arithmetic.control (arithmeticSlots slots) .variableCount) = _
    rw [clean.variableCount, List.append_nil]
  have hm : Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) =
        encodeWord input.equations.length := by
    change Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (prefixSlots slots 3) = _
    rw [Prefix.resultTapes_m]
    change encodeWord input.equations.length ++
      base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = _
    rw [clean.occurrenceCount, List.append_nil]
  have arithmetic := Arithmetic.inTime (arithmeticSlots slots) (fun l => labels (.inr l))
    exit program (fun l => atLabels (.inr l))
    (Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length)
    input.«variables» input.equations.length hn hm
    (clean.afterPrefix input.«variables» input.equations.length) ambient none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ parsed arithmetic
  have sourceEq : base (prefixSlots slots 0) = SourceEncoding.inputBits input := hinput
  simpa only [resultTapes, sourceEq] using joined

def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  Arithmetic.timePolynomial k s d noiseCount + Polynomial.C 3 * Polynomial.X + Polynomial.C 6

def inPolynomialTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.«variables» input.equations.length⟩)
      ((timePolynomial k s d noiseCount).eval (SourceEncoding.inputBits input).length) := by
  have run := inTime slots labels exit program atLabels base input hinput clean ambient register
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans run.steps_le_m
  have bound := Arithmetic.steps_le_timePolynomial k s d noiseCount
    input.«variables» input.equations.length (SourceEncoding.inputBits input).length
    (SourceEncoding.inputBits_length_ge_variables input) (SourceEncoding.inputBits_length_ge_equations input)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

end

end MaxCutGames.Reduction.MachineAddressHeaders

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTemplateAddress
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
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

theorem phaseTrace (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base)
    (baseField : base (slots .radix) = encodeWord B)
    (wordCorrect : MachineFieldTemplate.templateOutput tokens (fun j => base (slots (.field j))) =
      encodeWords values) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps tokens slots base B values]
      (some ⟨some (place (emitLabel (MachineFieldTemplate.startAt tokens.length 0))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (CanonicalAddress.radix B values)⟩ := by
  let emitted := MachineFieldTemplate.outputTapes base (slots .reversed) (encodeWords values)
  have emitRun := MachineFieldTemplate.phaseTrace tokens (fun j => slots (.field j))
    (slots .copyScratch) (slots .reversed)
    (fun _ => slots.injective.ne (by simp)) (fun _ => slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) (fun l => place (emitLabel l))
    (some (place reverseLabel)) P (fun l => atInstruction (emitLabel l))
    base clean.copyScratch ((ambient, ()), register)
  rw [wordCorrect] at emitRun
  change (MachineComposition.advance (TM2.step P))^[_] _ =
    some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩ at emitRun
  have reverseRun := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (slots .reversed) (slots .forward) (slots.injective.ne (by simp)) id false
    (place reverseLabel) (some (place (parseLabel (SourceFieldArray.startLabel width 0))))
    P (atInstruction reverseLabel) emitted (ambient, ()) none
  have reverseResult : MachineTransfer.tapesAt (slots .reversed) (slots .forward) emitted []
      ((emitted (slots .reversed)).reverse.map id ++ emitted (slots .forward)) =
      forwardTapes slots base values := by
    funext tape
    by_cases hr : tape = slots .reversed
    · subst tape
      simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
        slots.injective.ne (show Tape.reversed ≠ Tape.forward by simp), clean.reversed]
    · by_cases hf : tape = slots .forward
      · subst tape
        simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
          slots.injective.ne (show Tape.forward ≠ Tape.reversed by simp),
          clean.reversed, clean.forward]
      · simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt,
          forwardTapes, hr, hf]
  rw [reverseResult] at reverseRun
  have reverseLength : (emitted (slots .reversed)).length + 1 = (encodeWords values).length + 1 := by
    simp [emitted, MachineFieldTemplate.outputTapes, clean.reversed]
  rw [reverseLength] at reverseRun
  change (MachineComposition.advance (TM2.step P))^[(encodeWords values).length + 1]
    (some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩) =
    some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩ at reverseRun
  have parseRun := SourceFieldArray.sequenceTrace (slots .forward) (parseDestination slots)
    (fun r => place (parseLabel (SourceFieldArray.startLabel width r)))
    (fun r => place (parseLabel (SourceFieldArray.loopLabel width r)))
    (some (place (hornerLabel .start))) P (forwardTapes slots base values) 0 values []
    (by
      intro r hr
      simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
      exact slots.injective.ne (by simp))
    (by intro r hr; simpa using parse_atStart tokens slots place exit P atInstruction r (by omega))
    (by intro r hr; simpa using parse_atLoop tokens slots place exit P atInstruction r (by omega))
    (by simpa only [Nat.zero_add, hlen] using parse_atDone tokens slots place exit P atInstruction)
    (by simp [forwardTapes]) (ambient, ()) none
  change (MachineComposition.advance (TM2.step P))^[values.sum + 2 * values.length + 1]
    (some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩) =
    some ⟨some (place (hornerLabel .start)), ((ambient, ()), none),
      parsedTapes slots base values⟩ at parseRun
  have hbase : parsedTapes slots base values (hornerSlots slots (.inl 0)) = encodeWord B := by
    change parsedTapes slots base values (slots .radix) = _
    rw [parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
      (fun _ => slots.injective.ne (by simp))]
    exact baseField
  have hornerRun := MachineHorner.hornerTrace (hornerSlots slots) (fun l => place (hornerLabel l))
    (MachineDrainMany.entry (chosen slots) (fun l => place (cleanupLabel l)) exit)
    P (fun l => atInstruction (hornerLabel l)) (parsedTapes slots base values) B (digits values)
    hbase (parsedTapes_digit slots base values hlen clean)
    (parsedTapes_clean slots base values hlen clean) ambient none
  have cleanupRun := MachineDrainMany.trace (chosen slots) (fun l => place (cleanupLabel l)) exit
    P (fun l => atInstruction (cleanupLabel l)) (afterHorner slots base B values) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none, cleanup_result slots base B values hlen clean] at cleanupRun
  rw [show phaseSteps tokens slots base B values =
    MachineDrainMany.steps (chosen slots) (afterHorner slots base B values) +
      (MachineHorner.steps B (digits values) width +
      ((values.sum + 2 * values.length + 1) +
      (((encodeWords values).length + 1) +
      MachineFieldTemplate.templateSteps tokens (fun j => base (slots (.field j)))))) by
        unfold phaseSteps; omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := MachineHorner.steps B (digits values) width)]
  rw [Function.iterate_add_apply (m := values.sum + 2 * values.length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWords values).length + 1)]
  rw [emitRun, reverseRun, parseRun, hornerRun]
  exact cleanupRun

end Execution

end MaxCutGames.Reduction.MachineTemplateAddress

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

namespace MaxCutGames.Reduction.MachineAddressEdge

open Turing
open MaxCutGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

section Execution

variable (left right : List (MachineFieldTemplate.Token q)) (permutation : List Bool)
variable (slots : Tape q width ↪ K)
variable (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
variable (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction left right permutation slots place exit label)

include atInstruction

/-- Both actual address computations, a preserved-capacity copy, unary addition,
cleanup, two reverse transfers, and the fixed permutation instruction. -/
theorem phaseTrace (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base)
    (baseField : base (addressSlots slots .radix) = encodeWord B)
    (capacityField : base (capacityTape slots) = encodeWord C)
    (leftCorrect : MachineFieldTemplate.templateOutput left
      (fun j => base (addressSlots slots (.field j))) = encodeWords leftValues)
    (rightCorrect : MachineFieldTemplate.templateOutput right
      (fun j => base (addressSlots slots (.field j))) = encodeWords rightValues)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps left right slots base B C leftValues rightValues]
      (some ⟨some (place (leftLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt left.length 0)))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        appended slots base (edgeBits B C leftValues rightValues permutation)⟩ := by
  let L := CanonicalAddress.radix B leftValues
  let R := CanonicalAddress.radix B rightValues
  let afterLeft := appended slots base (encodeWord L)
  have cleanLeft : Clean slots afterLeft := Clean.appended slots base clean (encodeWord L)
  let rightResult := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft R
  let copied := Function.update rightResult (tempTape slots) (encodeWord C)
  let added := MachineUnaryAddAt.unaryTapes (tempTape slots) (workTape slots) copied 0 (C + R) [] []
  let shifted := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft (C + R)
  have leftRun := MachineTemplateAddress.phaseTrace left (addressSlots slots) (fun l => place (leftLabel l))
    (some (place (plumbing 0))) P (fun l => atInstruction (leftLabel l))
    base B leftValues leftLength clean.address baseField leftCorrect ambient register
  have transferLeft := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 0))
    (some (place (rightLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt right.length 0)))))
    P (atInstruction (plumbing 0)) (MachineTemplateAddress.resultTapes (addressSlots slots) base L) (ambient, ()) none
  rw [transfer_result slots base L clean.work] at transferLeft
  have leftWork : MachineTemplateAddress.resultTapes (addressSlots slots) base L (workTape slots) = encodeWord L := by
    simp only [addressResult_eq, Function.update_self, clean.work, List.append_nil]
  rw [leftWork] at transferLeft
  change (MachineComposition.advance (TM2.step P))^[(encodeWord L).length + 1]
    (some ⟨some (place (plumbing 0)), ((ambient, ()), none),
      MachineTemplateAddress.resultTapes (addressSlots slots) base L⟩) =
    some ⟨some (place (rightLabel (MachineTemplateAddress.emitLabel
      (MachineFieldTemplate.startAt right.length 0)))), ((ambient, ()), none), afterLeft⟩ at transferLeft
  have rightRun := MachineTemplateAddress.phaseTrace right (addressSlots slots) (fun l => place (rightLabel l))
    (some (place (plumbing 1))) P (fun l => atInstruction (rightLabel l))
    afterLeft B rightValues rightLength cleanLeft.address
    (by simpa [afterLeft] using baseField)
    (by simpa [afterLeft] using rightCorrect) ambient none
  have rightWork : rightResult (workTape slots) = encodeWord R := by
    simp only [rightResult, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  have rightTemp : rightResult (tempTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.forward
    · exact temp_ne_work slots
  have rightScratch : rightResult (scratchTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.copyScratch
    · exact slots.injective.ne (by simp)
  have rightCapacity : rightResult (capacityTape slots) = encodeWord C := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · simpa [afterLeft] using capacityField
    · exact slots.injective.ne (by simp)
  have copyRun := MachineCopy.copyTrace (capacityTape slots) (tempTape slots) (scratchTape slots)
    (slots.injective.ne (by simp)) (slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) false (place (plumbing 1)) (place (plumbing 2))
    (some (place (plumbing 3))) P (atInstruction (plumbing 1)) (atInstruction (plumbing 2))
    rightResult rightScratch (ambient, ()) none
  rw [rightCapacity, rightTemp, List.append_nil] at copyRun
  have addRun := MachineUnaryAddAt.addFromTapes (tempTape slots) (workTape slots)
    (temp_ne_work slots) (place (plumbing 3)) (some (place (plumbing 4)))
    P (atInstruction (plumbing 3)) copied C R [] []
    (by simp [copied])
    (by simp [copied, Ne.symm (temp_ne_work slots), rightWork]) (ambient, ()) none
  have addedTemp : added (tempTape slots) = encodeWord 0 := by
    simp [added, temp_ne_work]
  have drainResult : Function.update added (tempTape slots) [] = shifted := by
    funext tape
    by_cases ht : tape = tempTape slots
    · subst tape
      simp [shifted, addressResult_eq, temp_ne_work, show afterLeft (tempTape slots) = [] from cleanLeft.address.forward]
    · by_cases hw : tape = workTape slots
      · subst tape
        simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, shifted,
          addressResult_eq, Ne.symm (temp_ne_work slots), cleanLeft.work]
      · simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, copied,
          rightResult, shifted, addressResult_eq, ht, hw]
  have drainRun := (MachineDrain.drainInTime (tempTape slots) (place (plumbing 4))
    (some (place (plumbing 5))) P (atInstruction (plumbing 4)) added (ambient, ()) none).evals_in_steps
  change (MachineComposition.advance (TM2.step P))^[(added (tempTape slots)).length + 1]
    (some ⟨some (place (plumbing 4)), ((ambient, ()), none), added⟩) = _ at drainRun
  rw [addedTemp, drainResult] at drainRun
  have transferRight := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 5)) (some (place (plumbing 6))) P (atInstruction (plumbing 5))
    shifted (ambient, ()) none
  rw [transfer_result slots afterLeft (C + R) cleanLeft.work] at transferRight
  have shiftedWork : shifted (workTape slots) = encodeWord (C + R) := by
    simp only [shifted, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  rw [shiftedWork] at transferRight
  change (MachineComposition.advance (TM2.step P))^[(encodeWord (C + R)).length + 1]
    (some ⟨some (place (plumbing 5)), ((ambient, ()), none), shifted⟩) =
    some ⟨some (place (plumbing 6)), ((ambient, ()), none),
      appended slots afterLeft (encodeWord (C + R))⟩ at transferRight
  have finishRun := literalStep left right permutation slots place exit P atInstruction
    (appended slots afterLeft (encodeWord (C + R))) ((ambient, ()), none)
  have fullSteps : phaseSteps left right slots base B C leftValues rightValues =
      1 + (((encodeWord (C + R)).length + 1) + ((encodeWord 0).length + 1 +
      ((C + 1) + (2 * ((encodeWord C).length + 1) +
      (MachineTemplateAddress.phaseSteps right (addressSlots slots) afterLeft B rightValues +
      (((encodeWord L).length + 1) + MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues)))))) := by
    simp only [encodeWord_length]
    dsimp only [phaseSteps, L, R, afterLeft]
    omega
  rw [fullSteps]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (encodeWord (C + R)).length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWord 0).length + 1)]
  rw [Function.iterate_add_apply (m := C + 1)]
  rw [Function.iterate_add_apply (m := 2 * ((encodeWord C).length + 1))]
  rw [Function.iterate_add_apply (m := MachineTemplateAddress.phaseSteps right (addressSlots slots)
    afterLeft B rightValues)]
  rw [Function.iterate_add_apply (m := (encodeWord L).length + 1)]
  rw [leftRun, transferLeft, rightRun, copyRun, addRun, drainRun, transferRight]
  simp only [Function.iterate_one, MachineComposition.advance_some]
  rw [finishRun]
  simp only [MachineFieldTemplate.reset, afterLeft, appended_append]
  simp [edgeBits, encodeWords, L, R, List.append_assoc]

end Execution

end MaxCutGames.Reduction.MachineAddressEdge

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressTupleLoaded
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Integration.AddressTupleCleanup

open Turing MaxCutGames.Reduction MaxCutGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

variable {Λ : Type}

theorem trace (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[steps k s d noiseCount base]
      (some ⟨entry k s d noiseCount labels exit, (control, register), base⟩) =
    some ⟨exit, (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
      cleared k s d noiseCount base⟩ :=
  MachineDrainMany.trace (loadedFields k s d noiseCount) labels exit program atLabels
    base control register

noncomputable def execution (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry k s d noiseCount labels exit, (control, register), base⟩
      (some ⟨exit,
        (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
        cleared k s d noiseCount base⟩) (budget k s d noiseCount base) where
  steps := steps k s d noiseCount base
  evals_in_steps := trace k s d noiseCount labels exit program atLabels base control register
  steps_le_m := steps_le k s d noiseCount base

end MaxCutGames.Integration.AddressTupleCleanup

/-!
# The exact frame after a tuple body and its field cleanup

Loading replaces the initially empty equation-field tapes. Appending writes
only the shared reversed-output header, which is outside those fields. The
actual field drains therefore restore the original arena with precisely the
same appended bytes. Saved occurrence indices and the odometer survive.
-/

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

/-- The generic finite-sequence local obligation is discharged by the concrete
edge program, including its address arithmetic and capacity restoration. -/
theorem sequenceTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ))
    (atInstruction : ∀ label, P (place label) = sequenceInstruction slots rows place exit label)
    (base : K → List Bool) (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values rows base) (ambient : σ) :
    (MachineComposition.advance (TM2.step P))^[(rowCosts slots B C values rows base).sum]
      (some ⟨MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) rows place exit,
        ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineAddressEdge.appended slots base (rows.flatMap (payload B C values))⟩ := by
  have h := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) (rowResult slots B C values) (rowCost slots B C values)
    P (Invariant slots B C values rows) (fun _ => ((ambient, ()), none)) id rows
    (by
      intro row _ frame hframe
      exact Invariant.appended slots B C values rows frame hframe (payload B C values row))
    (by
      intro row hrow labels next placement frame hframe
      exact MachineAddressEdge.phaseTrace row.left row.right row.permutation slots
        labels next P placement frame B C (values row).left (values row).right
        (values row).left_length (values row).right_length hframe.clean hframe.radix
        hframe.capacity (hframe.correct row hrow).1 (hframe.correct row hrow).2 ambient none)
    place exit atInstruction base valid
  simpa only [sequence_steps, sequence_result, id_eq] using h

theorem phaseTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    (MachineComposition.advance (TM2.step P))^[
      (rowCosts slots B C values (selected rows rhs) base).sum + 1]
      (some ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) =
      some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩ := by
  have first := dispatcherStep slots rows place exit P (atInstruction (.inl ()))
    base rhs ambient register
  have rest := sequenceTrace slots (selected rows rhs) (fun l => place (.inr ⟨rhs, l⟩))
    exit P (fun l => atInstruction (.inr ⟨rhs, l⟩)) base B C values valid (rhs, ambient)
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[_]
    (TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) = _
  rw [first]
  exact rest

def phaseInTime (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩
      (some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩)
      ((rowCosts slots B C values (selected rows rhs) base).sum + 1) where
  steps := (rowCosts slots B C values (selected rows rhs) base).sum + 1
  evals_in_steps := phaseTrace slots rows place exit P atInstruction base rhs ambient register
    B C values valid
  steps_le_m := Nat.le_refl _

end MaxCutGames.Reduction.MachineOutcomeRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressGame
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable direct addresses for the actual canonical game. Every original
edge occurrence and its translation table is retained, in the same order.
Addresses not representing realized bodies are isolated vertices. No vertex
list, duplicate removal, or inverse enumeration is evaluated by the output. -/

namespace MaxCutGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

variable {rows : Rows k}

noncomputable def run (rows : Rows k) (labels : Label k s d noiseCount rows → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction rows labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (valid : MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main rows)), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩)
      (budget rows B C values F tuple base) := by
  have sourceRun := MachineSourceTuple.placedLoadUnaryInTime
    (sourceLabels labels) (some (rhsLabel labels)) P (fun l => atLabels (.inl l))
    F tuple base ready.source ready.saved ready.index ready.work ready.scratch ready.copy (oldRhs, ())
  have rhsRun := MachineRhsLoad.loadInTime (rhsField k s d noiseCount)
    (rhsLabel labels) (some (rowLabels labels (.inl ()))) P (atLabels (.inr (.inl ())))
    (((oldRhs, ()), ()), none) (loaded F tuple base) (rhs F tuple) (fun _ => [])
    (by
      intro j
      change loaded F tuple base (MachineSourceTuple.rhsField j) = _
      rw [loaded, MachineSourceTuple.output_rhs]
      change encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++
        base (.field j 3) = _
      rw [ready.fields j 3]
      rfl)
  have rowsRun := MachineOutcomeRows.phaseInTime (Slots k s d noiseCount) rows
    (rowLabels labels)
    (AddressTupleCleanup.entry k s d noiseCount (cleanupLabels labels) (some (resetLabel labels)))
    P (fun l => atLabels (.inr (.inr (.inl l))))
    (loaded F tuple base) (rhs F tuple) () none B C values valid
  have cleanupRun := AddressTupleCleanup.execution k s d noiseCount
    (cleanupLabels labels) (some (resetLabel labels)) P
    (fun l => atLabels (.inr (.inr (.inr (.inl l)))))
    (emitted rows B C values F tuple base) (((rhs F tuple), ()), ()) none
  simp only [MachineDrainMany.finalRegister_none] at cleanupRun
  have resetRun : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (resetLabel labels), ((((rhs F tuple), ()), ()), none),
        finalTapes rows B C values F tuple base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step P ⟨some (resetLabel labels), _, _⟩ = _
    change some (TM2.stepAux (P (resetLabel labels)) _ _) = _
    rw [show P (resetLabel labels) = reset exit from atLabels (.inr (.inr (.inr (.inr ()))))]
    cases exit <;> rfl
  have first := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ sourceRun rhsRun
  have second := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ first rowsRun
  have third := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ second cleanupRun
  have last := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ third resetRun
  refine { steps := last.steps, evals_in_steps := last.evals_in_steps, steps_le_m := ?_ }
  exact last.steps_le_m.trans (by dsimp only [budget]; omega)

/-- Actual fixed-row execution. Physical readiness and stored header values
are its only data hypotheses; no template or body-execution premise remains. -/
noncomputable def run_fixed_rows (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k,
        finalTapes (AddressOutcomeSpecs.rows k T) B C
          (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base⟩)
      (budget (AddressOutcomeSpecs.rows k T) B C
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) :=
  run (AddressOutcomeSpecs.rows k T) labels exit P atLabels F tuple base ready oldRhs B C
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (actualInvariant F tuple T base ready clean B C hB hC)

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      (budget (AddressOutcomeSpecs.rows k T)
        (CanonicalAddress.base F.«variables» F.equations.length s d)
        (AddressGame.bodyCapacity (source F) k s d)
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) := by
  have actual := run_fixed_rows T labels exit P atLabels F tuple base ready clean oldRhs
    (CanonicalAddress.base F.«variables» F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d) hB hC
  rw [finalTapes_eq _ _ _ _ F tuple base ready, tupleBits_actual] at actual
  exact actual

end MaxCutGames.Integration.AddressTupleBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

/-- The complete actual run, including the physical cleanup and output reversal. -/
noncomputable def outputInTime (C n q Q : Nat) (body : List Bool) :
    TM2OutputsInTime (machine C) (encodeWords [n, q, Q] ++ body)
      (some (outputBits C n q Q body))
      ((timePolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let initialRun := prefixInTime C n q Q body
  let bridge := finishStartInTime C (afterEmit C n q Q body)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun bridge
  let prefixRun : StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState,
        afterEmit C n q Q body⟩)
      ((prefixPolynomial C + 1).eval (encodeWords [n, q, Q] ++ body).length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm]
      using joined.steps_le_m }
  have hout : afterEmit C n q Q body .output = [] := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  let finish := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (C := C)) none (program C) (fun _ => rfl)
    (afterEmit C n q Q body) hout ((), ()) none
  let whole := SourceRuntimeSpace.prefixAndFinishInTime (machine C)
    (encodeWords [n, q, Q] ++ body) (prefixPolynomial C + 1) prefixRun
    clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys covers (afterEmit C n q Q body) hout (fun _ => rfl) finish
  have hword : (afterEmit C n q Q body .accumulator).reverse = outputBits C n q Q body := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  change StateTransition.EvalsToInTime (machine C).step _
    (some (haltList (machine C) (outputBits C n q Q body))) _
  rw [haltList_eq, ← hword]
  exact whole

/-- A fixed actual program works for every game and every alphabet size. -/
noncomputable def computation {q : Nat} (C : Nat) (hC : 0 < C) :
    TM2ComputableInPolyTime gameBits gameBits (UniformTarget.construct (q := q) C hC) where
  tm := machine C
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial C
  outputsFun g := by
    change TM2OutputsInTime (machine C) ((gameBits g).map id)
      (some ((gameBits (UniformTarget.construct C hC g)).map id)) _
    have hi := @List.map_id ((machine C).Γ (machine C).k₀) (gameBits g)
    have ho := @List.map_id ((machine C).Γ (machine C).k₁)
      (gameBits (UniformTarget.construct C hC g))
    simp only [hi, ho]
    rw [UniformTarget.gameBits_construct]
    have input : gameBits g = encodeWords [g.vertices, q, g.constraints.length] ++
        encodeWords (g.constraints.flatMap constraintWords) := by
      simp [gameBits, gameWords, encodeWords, List.append_assoc]
    rw [input]
    exact outputInTime C g.vertices q g.constraints.length
      (encodeWords (g.constraints.flatMap constraintWords))

theorem finiteAlphabet {q : Nat} (C : Nat) (hC : 0 < C) :
    MachineFiniteAlphabet.FiniteAlphabet (computation (q := q) C hC).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

end MaxCutGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Lookup
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

def headLookupCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  2 * ((tableBits table).length + 1) +
    2 * ((encodeWord (headIndex table e).val).length + 1) + tableTailCost table (headIndex table e)

theorem headLookupCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    headLookupCost table e ≤ 7 * (tableBits table).length + 5 := by
  have hi : (encodeWord (headIndex table e).val).length ≤ (tableBits table).length := by
    rw [encodeWord_length]
    exact (Nat.succ_le_of_lt (headIndex table e).isLt).trans (darts_le_tableBits_length table)
  have hl := tableTailCost_le table (headIndex table e)
  unfold headLookupCost
  omega

def headLookupInTime {q : Nat}
    (tape : HeadTapes K) (hinj : Function.Injective tape)
    (tableFirst tableSecond indexFirst indexSecond headerVertices headerDarts : Λ)
    (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTableFirst : P tableFirst = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 5) id false tableFirst (some tableSecond))
    (atTableSecond : P tableSecond = MachineCopy.forkLoop
      (tape 5) (tape 0) (tape 2) false tableSecond (some indexFirst))
    (atIndexFirst : P indexFirst = Reduction.MachineTransfer.loopAt
      (tape 1) (tape 5) id false indexFirst (some indexSecond))
    (atIndexSecond : P indexSecond = MachineCopy.forkLoop
      (tape 5) (tape 1) (tape 3) false indexSecond (some headerVertices))
    (atVertices : P headerVertices = MachineLookup.discard (tape 2) headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard (tape 2) headerDarts (labels .guard))
    (atStatement : ∀ label,
      P (labels label) = statement q (tape 3) (tape 2) (tape 4) labels exit label)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (hTable : base (tape 0) = tableBits table)
    (hReverse : base (tape 1) = encodeWord (headIndex table e).val)
    (hHead : base (tape 4) = []) (hScratch : base (tape 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (headTimePolynomial.eval (tableBits table).length) := by
  have hne (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (hinj heq)
  let t₁ := Function.update base (tape 2) (tableBits table ++ base (tape 2))
  let t₂ := Function.update t₁ (tape 3) (encodeWord (headIndex table e).val ++ base (tape 3))
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨some indexFirst, (ambient, none), t₁⟩)
      (2 * ((tableBits table).length + 1)) := by
    simpa only [hTable, t₁] using MachineCopy.copyInTime (tape 0) (tape 2) (tape 5)
      (hne 0 2 (by decide)) (hne 0 5 (by decide)) (hne 2 5 (by decide)) false
      tableFirst tableSecond (some indexFirst) P atTableFirst atTableSecond
      base hScratch ambient register
  have hsrc : t₁ (tape 1) = encodeWord (headIndex table e).val := by
    simp only [t₁, Function.update_of_ne (hne 1 2 (by decide)), hReverse]
  have hdst : t₁ (tape 3) = base (tape 3) := by
    simp only [t₁, Function.update_of_ne (hne 3 2 (by decide))]
  have hscratch₁ : t₁ (tape 5) = [] := by
    simp only [t₁, Function.update_of_ne (hne 5 2 (by decide)), hScratch]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some indexFirst, (ambient, none), t₁⟩
      (some ⟨some headerVertices, (ambient, none), t₂⟩)
      (2 * ((encodeWord (headIndex table e).val).length + 1)) := by
    simpa only [hsrc, hdst, t₂] using MachineCopy.copyInTime (tape 1) (tape 3) (tape 5)
      (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide)) false
      indexFirst indexSecond (some headerVertices) P atIndexFirst atIndexSecond
      t₁ hscratch₁ ambient none
  have ht₂ : t₂ = MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
      (encodeWord (headIndex table e).val ++ base (tape 3))
      (tableBits table ++ base (tape 2)) [] := by
    funext k
    by_cases hi : k = tape 3
    · subst k
      simp [t₂, MachineLookup.tapes, hne 3 2 (by decide), hne 3 4 (by decide)]
    · by_cases hs : k = tape 2
      · subst k
        simp [t₂, t₁, MachineLookup.tapes, hne 2 3 (by decide), hne 2 4 (by decide)]
      · by_cases hh : k = tape 4
        · subst k
          simp [t₂, t₁, MachineLookup.tapes, hne 4 3 (by decide),
            hne 4 2 (by decide), hHead]
        · simp [t₂, t₁, MachineLookup.tapes, hi, hs, hh]
  let run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some headerVertices, (ambient, none), t₂⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (tableTailCost table (headIndex table e)) := {
    steps := tableTailCost table (headIndex table e)
    evals_in_steps := by
      change (advance (TM2.step P))^[tableTailCost table (headIndex table e)]
        (some ⟨some headerVertices, (ambient, none), t₂⟩) =
          some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩
      rw [ht₂]
      simpa only [headLookupTapes, headValue, tableTailCost, List.append_nil] using
        fullTableTailTrace (tape 3) (tape 2) (tape 4) labels exit
          headerVertices headerDarts P atStatement atVertices atDarts
          (hne 3 2 (by decide)) (hne 3 4 (by decide)) (hne 2 4 (by decide))
          base table (headIndex table e) (base (tape 3)) (base (tape 2)) [] ambient none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  have hb := headLookupCost_le table e
  simp only [headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold headLookupCost at hb
  omega

end MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineCleanup
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual cleanup of all six clause-field tapes followed by the global unary
index increment. The output accumulator, unread input, and other caller tapes
are preserved, and no additional finish instruction is assumed.
-/

/-! One complete clause iteration of the actual initial graph machine. -/

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

/-! Exact execution of the clause loop, in the original occurrence order. -/

/-! The actual finite machine computing the initial graph's full serialized
table. The runtime bound counts every parse, row, cleanup and output reversal. -/

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

section RelationReader

variable {K Λ σ : Type} {N : Nat}

def unaryBits (slots : List (Fin N)) (bits : Buffer N) : List Bool :=
  slots.flatMap fun i => encodeWord (GraphTables.bitWord (bits i))

theorem unaryBits_eq_encodeWords (slots : List (Fin N)) (bits : Buffer N) :
    unaryBits slots bits = encodeWords (slots.map fun i => GraphTables.bitWord (bits i)) := by
  induction slots with
  | nil => rfl
  | cons i slots ih => simpa only [unaryBits, List.flatMap_cons, List.map_cons,
      encodeWords] using congrArg (encodeWord (GraphTables.bitWord (bits i)) ++ ·) ih

variable [DecidableEq K]

/-- Exact stack and register semantics, retaining every unread suffix bit. -/
theorem stepAux_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readUnarySlots source slots next) (ambient, buffer)
        (Function.update tapes source (unaryBits slots bits ++ suffix)) =
      TM2.stepAux next (ambient, MachineFixedBlockMap.fill slots bits buffer)
        (Function.update tapes source suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readUnarySlots, unaryBits, MachineFixedBlockMap.fill]
  | cons i slots ih =>
      cases hi : bits i <;>
        simp only [readUnarySlots, unaryBits, List.flatMap_cons, hi,
          GraphTables.bitWord, Bool.false_eq_true, ite_false, ite_true, if_true, encodeWord,
          List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append,
          TM2.stepAux, Function.update_self, List.head?_cons, Option.getD_some,
          List.tail_cons, Function.update_idem, MachineFixedBlockMap.fill,
          List.foldl_cons]
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i false) tapes
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i true) tapes

theorem stepAux_readUnaryAll (source : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (readUnarySlots source (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes source suffix) := by
  have h := stepAux_readUnarySlots source (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes source (unaryBits (List.ofFn id) bits ++ suffix) = tapes := by
    simpa only [← hinput] using Function.update_eq_self source tapes
  rw [hin, MachineFixedBlockMap.fill_all] at h
  exact h

end RelationReader

theorem unaryBits_relation (relation : GraphTables.RelationTable) :
    unaryBits (List.ofFn id) (fun i => relation[i]) =
      encodeWords (GraphTables.relationWords relation) := by
  have h : List.ofFn (fun i : Fin 4096 => relation[i]) = relation.toList := by
    change List.ofFn (fun i : Fin 4096 => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [unaryBits_eq_encodeWords]
  unfold GraphTables.relationWords
  rw [← h]
  simp only [List.map_ofFn, Function.comp_def, id_eq]

section AmbientRelation

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_readRelationAt (source : K) (exit : Λ) (ambient : σ)
    (buffer : Buffer 4096) (unitState : Unit) (register : Option Bool)
    (relation : GraphTables.RelationTable) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = encodeWords (GraphTables.relationWords relation) ++ suffix) :
    TM2.stepAux (readRelationAt source exit) (((ambient, buffer), unitState), register) tapes =
      ⟨some exit, (((ambient, fun i => relation[i]), unitState), register),
        Function.update tapes source suffix⟩ := by
  change TM2.stepAux (MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit)))
    ((readerStateEquiv σ 4096) (((ambient, unitState), register), buffer)) tapes = _
  rw [MachineControl.stepAux_simulation]
  rw [stepAux_readUnaryAll source _ _ (fun i => relation[i]) tapes suffix
    (by simpa only [unaryBits_relation] using hinput)]
  rfl

end AmbientRelation

namespace Program

open PCP.AlphabetTable

theorem headerPlan_bits (vertices darts tail head row : Nat) (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords [6 * vertices + 36864 * darts, 40960 * darts] := by
  rw [headerPlan, List.flatMap_append, Emitter.affineCommands_bits,
    Emitter.affineCommands_bits]
  simp [Emitter.affineValue, values, encodeWords]
  rfl

/-- The head-access call is part of this concrete program, with its actual
finite labels and framed tape effects. Its data are read from the table. -/
def headPhaseInTime (headerPlan rowPlan : Plan) (base : Tape → List Bool)
    (table : GenericGraphTables.Table 64) (e : Fin table.darts)
    (hTable : base .archive = GenericGraphTables.tableBits table)
    (hReverse : base .reverseIndex = encodeWord (Lookup.headIndex table e).val)
    (hHead : base .head = []) (hScratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headTableFirst, ((ambient, ()), none), base⟩
      (some ⟨some .readRelation, ((ambient, ()), none),
        Lookup.headLookupTapes headRoles base table e⟩)
      (Lookup.headTimePolynomial.eval (GenericGraphTables.tableBits table).length) :=
  Lookup.headLookupInTime headRoles headRoles_injective
    .headTableFirst .headTableSecond .headIndexFirst .headIndexSecond
    .headHeaderVertices .headHeaderDarts Label.headLookup (some .readRelation)
    (program headerPlan rowPlan) rfl rfl rfl rfl rfl rfl (fun _ => rfl)
    base table e hTable hReverse hHead hScratch (ambient, ()) none

end Program

end MaxCutGames.Foundations.Complexity.FinalCNFMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFHeader
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

@[simp] theorem headerTimePolynomial_eval (length : Nat) :
    headerTimePolynomial.eval length = 25 * length + 52 := by
  simp [headerTimePolynomial]

/-- An actual entry-to-guard trace, valid for any unread row suffix and every
finite ambient buffer. No execution premise is supplied by the caller. -/
def headerInTime (rowPlan : Plan) (n m : Nat) (rowsBits : List Bool) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (encodeWords [n, m] ++ rowsBits)⟩
      (some ⟨some .guard, ((ambient, ()), none), headerResultTapes n m rowsBits⟩)
      (headerTimePolynomial.eval (encodeWords [n, m] ++ rowsBits).length) := by
  let word := encodeWords [n, m] ++ rowsBits
  let bits := encodeWords [6 * n + 36864 * m, 40960 * m]
  let b₀ := headerInputTapes word
  let b₁ := headerFrame word word [] [] [] [] [] []
  let b₂ := headerFrame (encodeWord m ++ rowsBits) word (encodeWord n) [] [] [] [] []
  let b₃ := headerFrame rowsBits word (encodeWord n) (encodeWord m) [] [] [] []
  let b₄ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) []
  let b₅ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) bits.reverse
  let b₆ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) [] (encodeWord 0) bits.reverse
  let b₇ := headerResultTapes n m rowsBits
  have h₀ : Function.update b₀ Tape.archive (b₀ .input ++ b₀ .archive) = b₁ := by
    funext tape; cases tape <;> simp [b₀, b₁, headerInputTapes, headerFrame]
  have h₁ : Hastad.SourceMachine.fieldTapes Tape.input Tape.vertices b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ .vertices) = b₂ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₁, b₂, headerFrame]
  have h₂ : Hastad.SourceMachine.fieldTapes Tape.input Tape.darts b₂
      rowsBits (encodeWord m ++ b₂ .darts) = b₃ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₂, b₃, headerFrame]
  have h₄ : Emitter.resultTapes Tape.accumulator b₄
      (Emitter.prefixBits (Emitter.listCommands headerPlan) (values n m 0 0 0)
        ambient headerPlan.length) = b₅ := by
    rw [Emitter.bits_listCommands, headerPlan_bits]
    funext tape; cases tape <;> simp [Emitter.resultTapes, b₄, b₅, bits, headerFrame]
  have h₅ : Function.update b₅ Tape.tail [] = b₆ := by
    funext tape; cases tape <;> simp [b₅, b₆, headerFrame]
  have h₆ : Function.update b₆ Tape.head [] = b₇ := by
    funext tape; cases tape <;> simp [b₆, b₇, headerResultTapes, bits, word, headerFrame]
  have hn : n ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  have hm : m ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  let p₀ := MachineCopy.copyInTime Tape.input Tape.archive Tape.scratch
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program headerPlan rowPlan) rfl rfl b₀ (by rfl) (ambient, ()) none
  have p₀' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none), b₀⟩
      (some ⟨some .startVertices, ((ambient, ()), none), b₁⟩) (2 * (word.length + 1)) := by
    have h := p₀
    rw [h₀] at h
    simpa only [show b₀ .input = word from rfl] using h
  let p₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.vertices (by decide)
    .startVertices .readVertices (some .startDarts) (program headerPlan rowPlan)
    rfl rfl b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, headerFrame, word, encodeWords, List.append_assoc]) (ambient, ()) none
  have p₁' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startVertices, ((ambient, ()), none), b₁⟩
      (some ⟨some .startDarts, ((ambient, ()), none), b₂⟩) (n + 2) := by
    simpa only [h₁] using p₁
  let p₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.darts (by decide)
    .startDarts .readDarts (some .seedIndex) (program headerPlan rowPlan)
    rfl rfl b₂ m rowsBits rfl (ambient, ()) none
  have p₂' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startDarts, ((ambient, ()), none), b₂⟩
      (some ⟨some .seedIndex, ((ambient, ()), none), b₃⟩) (m + 2) := by
    simpa only [h₂] using p₂
  let p₃ : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .seedIndex, ((ambient, ()), none), b₃⟩
      (some ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩) 1 := {
    steps := 1
    evals_in_steps := by
      simp only [Function.iterate_one]
      change TM2.step (program headerPlan rowPlan)
        ⟨some .seedIndex, ((ambient, ()), none), b₃⟩ = _
      have ht : Function.update (Function.update (Function.update b₃ Tape.rowIndex [false])
          Tape.tail [false]) Tape.head [false] = b₄ := by
        funext tape; cases tape <;> simp [b₃, b₄, headerFrame, encodeWord]
      simp only [TM2.step, program, TM2.stepAux]
      apply congrArg some
      exact congrArg (TM2.Cfg.mk _ _) ht
    steps_le_m := Nat.le_refl _ }
  let p₄ := Emitter.planInTime (Emitter.listCommands headerPlan) source Tape.scratch
    Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.header (some .headerClearTail) (program headerPlan rowPlan) (fun _ => rfl)
    (values n m 0 0 0) b₄
    (by intro i; fin_cases i <;> rfl) rfl ambient word.length
    (by
      intro i
      fin_cases i
      · exact hn
      · exact hm
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _)
  have p₄' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩
      (some ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩)
      (7 * (3 * (word.length + 1) + 3) + 1) := by
    have h := p₄
    rw [h₄] at h
    simpa only [headerPlan_length] using h
  let p₅ := MachineLookup.discardInTime Tape.tail .headerClearTail .headerClearHead
    (program headerPlan rowPlan) rfl b₅ 0 [] (by simp [b₅, headerFrame]) (ambient, ()) none
  have p₅' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩
      (some ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩) 1 := by
    simpa only [h₅] using p₅
  let p₆ := MachineLookup.discardInTime Tape.head .headerClearHead .guard
    (program headerPlan rowPlan) rfl b₆ 0 [] (by simp [b₆, headerFrame]) (ambient, ()) none
  have p₆' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩
      (some ⟨some .guard, ((ambient, ()), none), b₇⟩) 1 := by
    simpa only [h₆] using p₆
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀' p₁'
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂'
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄'
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆'
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change _ ≤ headerTimePolynomial.eval word.length
      rw [headerTimePolynomial_eval]
      omega }

/-- The unread graph rows in the actual graph codec. -/
def tableRowsBits (table : PCP.GenericGraphTables.Table 64) : List Bool :=
  encodeWords ((PCP.GenericGraphTables.rowList table).flatMap PCP.GenericGraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GenericGraphTables.Table 64) :
    PCP.GenericGraphTables.tableBits table =
      encodeWords [table.vertices, table.darts] ++ tableRowsBits table := by
  simp only [PCP.GenericGraphTables.tableBits, PCP.GenericGraphTables.tableWords,
    encodeWords_append, tableRowsBits]

/-- Specialization to the entire input of the actual numbered graph codec. -/
def tableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (PCP.GenericGraphTables.tableBits table)⟩
      (some ⟨some .guard, ((ambient, ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [tableBits_header_rows]
  exact headerInTime rowPlan table.vertices table.darts (tableRowsBits table) ambient

theorem headerInput_configuration (rowPlan : Plan) (input : List Bool) :
    initList (machine headerPlan rowPlan) input =
      ⟨some .copyFirst, ((((), fun _ => false), ()), none), headerInputTapes input⟩ := by
  have ht : (initList (machine headerPlan rowPlan) input).stk = headerInputTapes input := by
    funext tape
    cases tape <;> simp [initList, machine, headerInputTapes, headerFrame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- The same bounded phase begins at the machine's genuine initial configuration. -/
def initializedTableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64) :
    StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
      (initList (machine headerPlan rowPlan) (PCP.GenericGraphTables.tableBits table))
      (some ⟨some .guard, ((((), fun _ => false), ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [headerInput_configuration]
  exact tableHeaderInTime rowPlan table ((), fun _ => false)

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
Actual finite-machine execution of the final converter's row phases. These
certificates use the concrete program statements, preserve all other tapes,
and expose the precise concatenated output of the fixed emission plan.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

/-- Read the two fields actually stored in a graph row: tail and reverse dart. -/
def endpointsInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail reverse : Nat) (rest : List Bool)
    (hinput : base .input = encodeWord tail ++ encodeWord reverse ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .headTableFirst, ((ambient, ()), none),
        endpointTapes base tail reverse rest⟩) (tail + reverse + 4) := by
  let first := Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
    (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail)
  let run₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.tail (by decide)
    .startTail .readTail (some .startReverse) (program headerPlan plan) rfl rfl
    base tail (encodeWord reverse ++ rest) (by simpa only [List.append_assoc] using hinput)
    (ambient, ()) none
  have input₁ : first .input = encodeWord reverse ++ rest := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  have reverse₁ : first .reverseIndex = base .reverseIndex := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  let run₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.reverseIndex (by decide)
    .startReverse .readReverse (some .headTableFirst) (program headerPlan plan) rfl rfl
    first reverse rest input₁ (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  simpa only [first, reverse₁, endpointTapes, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using joined

/-- The fixed unary relation reader occupies one finite TM2 statement. -/
def relationInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (relation : GraphTables.RelationTable) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.relationWords relation) ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .readRelation, ((ambient, ()), none), base⟩
      (some ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((((), fun i => relation[i]), ()), none), Function.update base .input rest⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .readRelation) _ _) = _
    rw [program, stepAux_readRelationAt _ _ _ _ _ _ _ _ _ hinput]
  steps_le_m := Nat.le_refl _

/-- Execute the complete fixed row emission plan against physical unary tapes. -/
def emitInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (operands : Fin 5 → Nat) (hoperands : ∀ i, base (source i) = encodeWord (operands i))
    (hscratch : base .scratch = []) (ambient : Ambient)
    (N : Nat) (hbounded : ∀ i, operands i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨some .clearTail, ((ambient, ()), none),
        Function.update base .accumulator
          ((plan.flatMap (Emitter.commandBits operands ambient)).reverse ++ base .accumulator)⟩)
      (plan.length * (3 * (N + 1) + 3) + 1) := by
  have run := Emitter.planInTime (Emitter.listCommands plan)
    source Tape.scratch Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.row (some .clearTail) (program headerPlan plan) (fun _ => rfl)
    operands base hoperands hscratch ambient N hbounded
  simpa only [Emitter.bits_listCommands, Emitter.resultTapes] using run

/-- Clear precisely the three isolated temporary fields and increment the
physical row counter before returning to the input guard. -/
def finishInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail head reverse row : Nat)
    (htail : base .tail = encodeWord tail) (hhead : base .head = encodeWord head)
    (hreverse : base .reverseIndex = encodeWord reverse)
    (hrow : base .rowIndex = encodeWord row) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .clearTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩)
      (tail + head + reverse + 4) := by
  let t₁ := Function.update base Tape.tail []
  let t₂ := Function.update t₁ Tape.head []
  let t₃ := Function.update t₂ Tape.reverseIndex []
  let run₁ := MachineLookup.discardInTime Tape.tail .clearTail .clearHead
    (program headerPlan plan) rfl base tail [] (by simpa using htail) (ambient, ()) none
  have hhead₁ : t₁ .head = encodeWord head := by simp [t₁, hhead]
  let run₂ := MachineLookup.discardInTime Tape.head .clearHead .clearReverse
    (program headerPlan plan) rfl t₁ head [] (by simpa using hhead₁) (ambient, ()) none
  have hreverse₂ : t₂ .reverseIndex = encodeWord reverse := by simp [t₂, t₁, hreverse]
  let run₃ := MachineLookup.discardInTime Tape.reverseIndex .clearReverse .nextRow
    (program headerPlan plan) rfl t₂ reverse [] (by simpa using hreverse₂) (ambient, ()) none
  let run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .nextRow, ((ambient, ()), none), t₃⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program headerPlan plan .nextRow) _ _) = _
      simp only [program, TM2.stepAux]
      congr 2
      simp [t₃, t₂, t₁, finishTapes, hrow, encodeWord, List.replicate_succ]
    steps_le_m := Nat.le_refl _ }
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  have run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
# Structural conversion to the generic 64-label table format

The fixed and generic formats store exactly the same fields in the same order.
Conversion maps the row structure, keeping each endpoint, reversal index, and
relation vector unchanged. In particular, the serialized input bits are equal,
so the generic table lookup machine applies to the actual final-converter input.
-/

/-! Execution of one complete actual graph row in the final CNF machine. -/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

theorem prepared_input (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .input = rowRest table e rest := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_head (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .head =
      encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes,
    genericTable_headValue, GraphTables.semantics, ConstraintGraph.head,
    GraphTables.reverseAt]

theorem prepared_tail (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .tail = encodeWord table.rows[e].tail.val ++ base .tail := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_reverse (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .reverseIndex =
      encodeWord table.rows[e].reverseIndex.val ++ base .reverseIndex := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_frame (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork) :
    preparedTapes base table e rest tape = base tape := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes, hi, ht, hr, hh, hs, hx]

theorem rowResult_frame (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork)
    (ha : tape ≠ .accumulator) (hc : tape ≠ .rowIndex) :
    rowResultTapes plan base table e rest tape = base tape := by
  simp only [rowResultTapes, finishTapes, emittedTapes, Function.update_of_ne hi,
    Function.update_of_ne ht, Function.update_of_ne hr, Function.update_of_ne hh,
    Function.update_of_ne ha, Function.update_of_ne hc]
  exact prepared_frame base table e rest tape hi ht hr hh hs hx

def guardRowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input ≠ []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .startTail, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    cases hb : base .input with
    | nil => exact False.elim (hinput hb)
    | cons b bs => simp [program, guard, TM2.stepAux, hb]
  steps_le_m := Nat.le_refl _

def guardEndInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input = []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .reverseOutput, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    simp [program, guard, TM2.stepAux, hinput]
  steps_le_m := Nat.le_refl _

/-- All five unbounded operands remain isolated encoded naturals after the
row parser and head lookup, including both independently retrieved endpoints. -/
theorem prepared_operands (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hr : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) :
    ∀ i, (Function.update (preparedTapes base table e rest) Tape.input rest) (source i) =
      encodeWord (rowOperands table e i) := by
  intro i
  fin_cases i
  · simpa [source, rowOperands, values] using
      prepared_frame base table e rest .vertices (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) |>.trans hn
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.darts = _
    simp only [Function.update_of_ne (show Tape.darts ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hm
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.tail = _
    simp only [Function.update_of_ne (show Tape.tail ≠ Tape.input by decide), prepared_tail,
      ht, List.append_nil]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.head = _
    simp only [Function.update_of_ne (show Tape.head ≠ Tape.input by decide), prepared_head]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.rowIndex = _
    simp only [Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hr

theorem rowOperands_bounded (table : GraphTables.Table) (e : Fin table.darts) :
    ∀ i, rowOperands table e i ≤ (GraphTables.tableBits table).length := by
  intro i
  fin_cases i
  · exact GraphTables.vertices_le_tableBits_length table
  · exact GraphTables.darts_le_tableBits_length table
  · exact table.rows[e].tail.isLt.le.trans (GraphTables.vertices_le_tableBits_length table)
  · exact table.rows[table.rows[e].reverseIndex].tail.isLt.le.trans
      (GraphTables.vertices_le_tableBits_length table)
  · exact e.isLt.le.trans (GraphTables.darts_le_tableBits_length table)

def rowTime (plan : Plan) (N : Nat) : Nat :=
  plan.length * (3 * (N + 1) + 3) + 12 * N + 15

/-- Run one complete stored row, including the actual table-based head lookup.
The only hypotheses describe the physical input tapes; no execution or
serialization correctness of a caller-provided body is assumed. -/
noncomputable def rowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest)
    (harchive : base .archive = GraphTables.tableBits table)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hrow : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) (hh : base .head = []) (hr : base .reverseIndex = [])
    (hscratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((rowRelation table e, ()), none),
        rowResultTapes plan base table e rest⟩)
      (rowTime plan (GraphTables.tableBits table).length) := by
  let parsed := endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
    (rowRest table e rest)
  let ready := preparedTapes base table e rest
  let read := Function.update ready Tape.input rest
  let output := emittedTapes plan base table e rest
  let run₁ := endpointsInTime headerPlan plan base table.rows[e].tail.val
    table.rows[e].reverseIndex.val (rowRest table e rest)
    (by simpa [GraphTables.rowWords, encodeWords, List.append_assoc, rowRest] using hinput) ambient
  have parsed_archive : parsed .archive = GenericGraphTables.tableBits (genericTable table) := by
    simpa [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes] using harchive
  have parsed_reverse : parsed .reverseIndex =
      encodeWord (Lookup.headIndex (genericTable table) e).val := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hr]
  have parsed_head : parsed .head = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hh]
  have parsed_scratch : parsed .scratch = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hscratch]
  let run₂ := headPhaseInTime headerPlan plan parsed (genericTable table) e
    parsed_archive parsed_reverse parsed_head parsed_scratch ambient
  let run₃ := relationInTime headerPlan plan ready table.rows[e].relation rest
    (prepared_input base table e rest) ambient
  have read_operands : ∀ i, read (source i) = encodeWord (rowOperands table e i) :=
    prepared_operands base table e rest hn hm hrow ht
  have read_scratch : read .scratch = [] := by
    simp only [read, Function.update_of_ne (show Tape.scratch ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hscratch
  have read_acc : read .accumulator = base .accumulator := by
    simp only [read, Function.update_of_ne (show Tape.accumulator ≠ Tape.input by decide)]
    exact prepared_frame base table e rest .accumulator (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((rowRelation table e, ()), none), read⟩
      (some ⟨some .clearTail, ((rowRelation table e, ()), none), output⟩)
      (plan.length * (3 * ((GraphTables.tableBits table).length + 1) + 3) + 1) := by
    simpa only [read_acc, output, emittedTapes, read, ready] using
      emitInTime headerPlan plan read (rowOperands table e) read_operands read_scratch
        (rowRelation table e) (GraphTables.tableBits table).length (rowOperands_bounded table e)
  have output_tail : output .tail = encodeWord table.rows[e].tail.val := by
    simp [output, emittedTapes, prepared_tail, ht]
  have output_head : output .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
    simp [output, emittedTapes, prepared_head]
  have output_reverse : output .reverseIndex = encodeWord table.rows[e].reverseIndex.val := by
    simp [output, emittedTapes, prepared_reverse, hr]
  have output_row : output .rowIndex = encodeWord e.val := by
    simp only [output, emittedTapes,
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.accumulator by decide),
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hrow
  let run₅ := finishInTime headerPlan plan output table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val table.rows[e].reverseIndex.val e.val
    output_tail output_head output_reverse output_row (rowRelation table e)
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  let r₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃₄ run₅
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hb := run.steps_le_m
  have htbound := rowOperands_bounded table e 2
  have hhbound := rowOperands_bounded table e 3
  have hrbound := table.rows[e].reverseIndex.isLt.le.trans (GraphTables.darts_le_tableBits_length table)
  change table.rows[e].tail.val ≤ _ at htbound
  change table.rows[table.rows[e].reverseIndex].tail.val ≤ _ at hhbound
  simp only [Lookup.headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, genericTable_tableBits] at hb
  unfold rowTime
  omega

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFStream
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTableAdapter

def outputStream (plan : Plan) (table : GraphTables.Table)
    (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => plan.flatMap (Emitter.commandBits (rowOperands table e)
    (rowRelation table e)))

theorem remainingEvents_cons (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    remainingEvents table r = ⟨r, h⟩ :: remainingEvents table (r + 1) := by
  unfold remainingEvents
  rw [List.drop_eq_getElem_cons (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

@[simp] theorem inputStream_append (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    inputStream table (first ++ rest) = inputStream table first ++ inputStream table rest := by
  simp only [inputStream, List.flatMap_append]

@[simp] theorem outputStream_nil (plan : Plan) (table : GraphTables.Table) :
    outputStream plan table [] = [] := rfl

@[simp] theorem outputStream_cons (plan : Plan) (table : GraphTables.Table)
    (e : Fin table.darts) (events : List (Fin table.darts)) :
    outputStream plan table (e :: events) =
      plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e)) ++
        outputStream plan table events := rfl

@[simp] theorem outputStream_append (plan : Plan) (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    outputStream plan table (first ++ rest) =
      outputStream plan table first ++ outputStream plan table rest := by
  simp only [outputStream, List.flatMap_append]

theorem inputStream_remaining_cons (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    inputStream table (remainingEvents table r) =
      encodeWords (GraphTables.rowWords table.rows[(⟨r, h⟩ : Fin table.darts)]) ++
        inputStream table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, inputStream_cons]

theorem outputStream_remaining_cons (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (remainingEvents table r) =
      plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
        (rowRelation table ⟨r, h⟩)) ++
          outputStream plan table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, outputStream_cons]

theorem encodeWords_flatMap_rows_inline_FinalCNFStream {α : Type} (rows : List α) (words : α → List Nat) :
    encodeWords (rows.flatMap words) = rows.flatMap (fun row => encodeWords (words row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowList_eq_finRange_map (table : GraphTables.Table) :
    GraphTables.rowList table = (List.finRange table.darts).map (fun e => table.rows[e]) := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  change table.rows.toList = (Vector.ofFn (fun i => table.rows[i.val])).toList
  rw [Vector.ofFn_getElem]

/-- The stream starts at exactly the row suffix left by the checked header phase. -/
theorem inputStream_all (table : GraphTables.Table) :
    inputStream table (List.finRange table.darts) = tableRowsBits (genericTable table) := by
  rw [tableRowsBits, genericTable_rowList]
  erw [List.flatMap_map]
  change inputStream table (List.finRange table.darts) =
    encodeWords ((GraphTables.rowList table).flatMap
      (fun row => GenericGraphTables.rowWords (genericRow row)))
  simp only [genericRow_words]
  rw [rowList_eq_finRange_map, List.flatMap_map, encodeWords_flatMap_rows_inline_FinalCNFStream]
  rfl

theorem inputStream_remaining_zero (table : GraphTables.Table) :
    inputStream table (remainingEvents table 0) = tableRowsBits (genericTable table) := by
  rw [remainingEvents_zero, inputStream_all]

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-! The actual bounded loop over every stored row of the final CNF converter. -/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

structure LoopInvariant (table : GraphTables.Table) (r : Nat) (base : Tape → List Bool) : Prop where
  input : base .input = inputStream table (remainingEvents table r)
  archive : base .archive = GraphTables.tableBits table
  vertices : base .vertices = encodeWord table.vertices
  darts : base .darts = encodeWord table.darts
  index : base .rowIndex = encodeWord r
  tail : base .tail = []
  head : base .head = []
  reverse : base .reverseIndex = []
  scratch : base .scratch = []

structure LoopRun (headerPlan plan : Plan) (table : GraphTables.Table) (r remaining : Nat)
    (base : Tape → List Bool) (ambient : Ambient) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
    ⟨some .guard, ((ambient, ()), none), base⟩
    (some ⟨some .reverseOutput, ((finalAmbient, ()), none), finalTapes⟩)
    (remaining * (rowTime plan (GraphTables.tableBits table).length + 1) + 1)
  accumulator : finalTapes .accumulator =
    (outputStream plan table (remainingEvents table r)).reverse ++ base .accumulator
  output : finalTapes .output = base .output

theorem rowInvariant_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (hr : r < table.darts) (base : Tape → List Bool) (invariant : LoopInvariant table r base) :
    LoopInvariant table (r + 1)
      (rowResultTapes plan base table ⟨r, hr⟩
        (inputStream table (remainingEvents table (r + 1)))) := by
  constructor
  · exact rowResult_input _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .archive (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.archive
  · exact (rowResult_frame _ _ _ _ _ .vertices (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.vertices
  · exact (rowResult_frame _ _ _ _ _ .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.darts
  · exact rowResult_index _ _ _ _ _
  · exact rowResult_tail _ _ _ _ _
  · exact rowResult_head _ _ _ _ _
  · exact rowResult_reverse _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.scratch

theorem rowWords_nonempty (table : GraphTables.Table) (e : Fin table.darts) :
    encodeWords (GraphTables.rowWords table.rows[e]) ≠ [] := by
  simp [GraphTables.rowWords, encodeWords, encodeWord]

/-- Induction follows the actual unary row counter and the actual unconsumed
input suffix. Every iteration invokes the checked row program. -/
noncomputable def loopInTime (headerPlan plan : Plan) (table : GraphTables.Table)
    (remaining : Nat) :
    ∀ (r : Nat) (_hcount : r + remaining = table.darts) (base : Tape → List Bool)
      (ambient : Ambient), LoopInvariant table r base →
        LoopRun headerPlan plan table r remaining base ambient := by
  induction remaining with
  | zero =>
      intro r hcount base ambient invariant
      have hr : r = table.darts := by omega
      have hinput : base .input = [] := by
        simpa only [hr, remainingEvents_done, inputStream_nil] using invariant.input
      refine {
        finalAmbient := ambient
        finalTapes := base
        execution := ?_
        accumulator := ?_
        output := rfl }
      · simpa only [Nat.zero_mul, Nat.zero_add] using
          guardEndInTime headerPlan plan base ambient hinput
      · simp only [hr, remainingEvents_done, outputStream_nil, List.reverse_nil, List.nil_append]
  | succ remaining ih =>
      intro r hcount base ambient invariant
      have hr : r < table.darts := by omega
      let e : Fin table.darts := ⟨r, hr⟩
      let rest := inputStream table (remainingEvents table (r + 1))
      let next := rowResultTapes plan base table e rest
      have hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest := by
        rw [invariant.input, inputStream_remaining_cons table r hr]
      have hnonempty : base .input ≠ [] := by
        rw [hinput]
        exact List.append_ne_nil_of_left_ne_nil (rowWords_nonempty table e) rest
      let guardRun := guardRowInTime headerPlan plan base ambient hnonempty
      let rowRun := rowInTime headerPlan plan base table e rest hinput invariant.archive
        invariant.vertices invariant.darts invariant.index invariant.tail invariant.head
        invariant.reverse invariant.scratch ambient
      let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guardRun rowRun
      let later := ih (r + 1) (by omega) next (rowRelation table e)
        (rowInvariant_succ plan table r hr base invariant)
      let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first later.execution
      refine {
        finalAmbient := later.finalAmbient
        finalTapes := later.finalTapes
        execution := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
        accumulator := ?_
        output := ?_ }
      · have hb := run.steps_le_m
        rw [Nat.succ_mul]
        omega
      · rw [later.accumulator, outputStream_remaining_cons plan table r hr]
        simp only [next, rowResult_accumulator, List.reverse_append, List.append_assoc]
        rfl
      · rw [later.output]
        exact rowResult_frame _ _ _ _ _ .output (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes before the
canonical halt required by the machine interface.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def emittedBytes (plan : Plan) (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts] ++
    outputStream plan table (List.finRange table.darts)

noncomputable def rawBudget (plan : Plan) (table : GraphTables.Table) : Nat :=
  headerTimePolynomial.eval (GraphTables.tableBits table).length +
    table.darts * (rowTime plan (GraphTables.tableBits table).length + 1) + 1 +
      (emittedBytes plan table).length + 1

structure RawRun (plan : Plan) (table : GraphTables.Table) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (machine headerPlan plan).step
    (initList (machine headerPlan plan) (GraphTables.tableBits table))
    (some ⟨none, ((finalAmbient, ()), none), finalTapes⟩) (rawBudget plan table)
  output : finalTapes .output = emittedBytes plan table

theorem header_loopInvariant (_plan : Plan) (table : GraphTables.Table) :
    LoopInvariant table 0 (headerResultTapes table.vertices table.darts
      (tableRowsBits (genericTable table))) := by
  constructor
  · rw [headerResultTapes_input, inputStream_remaining_zero]
  · rw [headerResultTapes_archive]
    exact (tableBits_header_rows (genericTable table)).symm.trans (genericTable_tableBits table)
  · rfl
  · rfl
  · exact headerResultTapes_rowIndex _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

/-- The input is read from the genuine `initList` configuration. Header, every
row, final guard, and reversal are all actual transitions of this one program. -/
noncomputable def rawRun (plan : Plan) (table : GraphTables.Table) : RawRun plan table := by
  let base := headerResultTapes table.vertices table.darts (tableRowsBits (genericTable table))
  let ambient : Ambient := ((), fun _ => false)
  have headerRun : StateTransition.EvalsToInTime (machine headerPlan plan).step
      (initList (machine headerPlan plan) (GraphTables.tableBits table))
      (some ⟨some .guard, ((ambient, ()), none), base⟩)
      (headerTimePolynomial.eval (GraphTables.tableBits table).length) := by
    simpa only [genericTable_tableBits, genericTable_vertices, genericTable_darts, base, ambient]
      using initializedTableHeaderInTime plan (genericTable table)
  let loop := loopInTime headerPlan plan table table.darts 0 (by omega)
    base ambient (header_loopInvariant plan table)
  have acc : loop.finalTapes .accumulator = (emittedBytes plan table).reverse := by
    rw [loop.accumulator]
    simp only [remainingEvents_zero, base, headerResultTapes_accumulator, emittedBytes,
      List.reverse_append]
  have out : loop.finalTapes .output = [] := by
    rw [loop.output]
    rfl
  let finalTapes := Reduction.MachineTransfer.tapesAt Tape.accumulator Tape.output
    loop.finalTapes [] (emittedBytes plan table)
  have finish : StateTransition.EvalsToInTime (machine headerPlan plan).step
      ⟨some .reverseOutput, ((loop.finalAmbient, ()), none), loop.finalTapes⟩
      (some ⟨none, ((loop.finalAmbient, ()), none), finalTapes⟩)
      ((emittedBytes plan table).length + 1) := by
    have run := Reduction.MachineTransfer.transferAtInTime Tape.accumulator Tape.output
      (by decide) id false .reverseOutput none (program headerPlan plan) rfl
      loop.finalTapes (loop.finalAmbient, ()) none
    simpa only [acc, out, List.reverse_reverse, List.length_reverse, List.map_id,
      List.append_nil, finalTapes, machine, FinTM2.step] using! run
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headerRun loop.execution
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  exact {
    finalAmbient := loop.finalAmbient
    finalTapes := finalTapes
    execution := {
      toEvalsTo := run.toEvalsTo
      steps_le_m := by
        have hb := run.steps_le_m
        unfold rawBudget
        omega }
    output := by simp [finalTapes, Reduction.MachineTransfer.tapesAt] }

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows. Their machine execution
is proved separately in FinalCNFRow and FinalCNFComputation.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def instantiateLiteral (literal : LiteralTemplate) : Literal (VerifierToCNF.outputVariables V) :=
  ⟨resolve V e p literal.reference, literal.positive⟩

def instantiateClause (clause : ClauseTemplate) : Clause (VerifierToCNF.outputVariables V) :=
  #v[instantiateLiteral V e p clause[0], instantiateLiteral V e p clause[1],
    instantiateLiteral V e p clause[2]]

/-- A symbolic twelve-input chain expands to exactly these ten clauses. -/
theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

/-- Instantiating the fixed plan reproduces the actual converter's entire block. -/
theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem instantiateClause_words (clause : ClauseTemplate) :
    Complexity.clauseWords (instantiateClause V e p clause) =
      clauseWords (fun r => (resolve V e p r).val) clause := rfl

/-- The finite plan's sixty natural fields are the converter's actual row words. -/
theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

end MaxCutGames.Foundations.Complexity.FinalCNFTemplate

/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

/-- Seven real commands for the two unary fields of a literal. -/
def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternLiteral (p : VerifierToCNF.PatternIndex 12) (clause : Fin 10) (slot : Fin 3)
    (ambient : Ambient) : LiteralTemplate :=
  literalAt (ambient.2 (FinalCNFPattern.patternRelationIndex p))
    (VerifierToCNF.patternAt 12 p) clause slot

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]; norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true, if_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFOutput
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).«variables»,
      (FinalTableFormula.output table).clauses.length] := by
  simp only [formulaHeader, FinalTableFormula.variable_count, FinalTableFormula.clause_count,
    Nat.mul_comm]

theorem outputStream_eq_clauseBits (table : GraphTables.Table) :
    outputStream rowPlan table (List.finRange table.darts) =
      encodeWords ((FinalTableFormula.output table).clauses.flatMap Complexity.clauseWords) := by
  calc
    _ = (List.finRange table.darts).flatMap (fun e =>
          encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) := by
      apply List.flatMap_congr
      intro e he
      exact rowPlan_bits table e
    _ = encodeWords ((List.finRange table.darts).flatMap (fun e =>
          (VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) :=
      (encodeWords_flatMap _ _).symm
    _ = _ := by
      congr 1
      rw [← List.flatMap_assoc]
      rfl

theorem header_append_outputStream (table : GraphTables.Table) :
    formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts) =
      formulaBits (FinalTableFormula.output table) := by
  rw [formulaHeader_eq, outputStream_eq_clauseBits]
  exact (encodeWords_append _ _).symm

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP

theorem rowTimePolynomial_eval (N : Nat) :
    rowTimePolynomial.eval N = rowTime rowPlan N := by
  simp only [rowTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTime, rowPlan_length]

/-- Header, at most `N` rows with guards, and the final output reversal. -/
noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

theorem phaseTimePolynomial_eval (N : Nat) :
    phaseTimePolynomial.eval N =
      headerTimePolynomial.eval N + (N * (rowTime rowPlan N + 1) + 1) +
        (FinalTableFormula.sizePolynomial.eval N + 1) := by
  simp only [phaseTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTimePolynomial_eval]

theorem phaseTime_le {N rows outputLength : Nat} (rowBound : rows ≤ N)
    (outputBound : outputLength ≤ FinalTableFormula.sizePolynomial.eval N) :
    headerTimePolynomial.eval N + (rows * (rowTime rowPlan N + 1) + 1) +
      (outputLength + 1) ≤ phaseTimePolynomial.eval N := by
  have hrows := Nat.mul_le_mul_right (rowTime rowPlan N + 1) rowBound
  rw [phaseTimePolynomial_eval]
  omega

/-- The bound specialized to the actual table and actual formula serialization. -/
theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

/-- Twelve private stacks are drained, then the finite state is reset.
`C` is the fixed maximum number of pushes in a raw-program transition. -/
noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

namespace MaxCutGames.Foundations.Complexity.FinalCNFCleanup

open Turing MachineComposition
open FinalCNFMachine (State)
open FinalCNFMachine.Program (Tape Plan)

/-- The raw machine has thirteen tapes. These are precisely the twelve
non-output tapes, including the original input and retained archive. -/
def chosen : List Tape :=
  [.input, .accumulator, .scratch, .vertices, .darts, .tail, .head,
    .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

@[simp] theorem chosen_length : chosen.length = 12 := rfl

@[simp] theorem mem_chosen (tape : Tape) : tape ∈ chosen ↔ tape ≠ .output := by
  cases tape <;> simp [chosen]

abbrev Label (headerPlan rowPlan : Plan) :=
  FinalCNFMachine.Program.Label headerPlan.length rowPlan.length ⊕
    (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (headerPlan rowPlan : Plan) : MachineDrainMany.Label chosen → Label headerPlan rowPlan :=
  fun label => .inr (.inl label)

def resetLabel (headerPlan rowPlan : Plan) : Label headerPlan rowPlan := .inr (.inr ())

def cleanupEntry (headerPlan rowPlan : Plan) : Option (Label headerPlan rowPlan) :=
  MachineDrainMany.entry chosen (cleanupLabel headerPlan rowPlan) (some (resetLabel headerPlan rowPlan))

def completedProgram (headerPlan rowPlan : Plan) : Label headerPlan rowPlan →
    TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan rowPlan) (State Unit)
  | .inl label => redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
      (FinalCNFMachine.Program.program headerPlan rowPlan label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) label
  | .inr (.inr _) => .load (fun _ => (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState) .halt

def completedMachine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan rowPlan
  main := .inl .copyFirst
  σ := State Unit
  initialState := (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState
  m := completedProgram headerPlan rowPlan

def embeddedCfg (headerPlan rowPlan : Plan)
    (cfg : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg) :
    (completedMachine headerPlan rowPlan).Cfg :=
  redirectCfg Sum.inl (cleanupEntry headerPlan rowPlan) cfg

theorem step_simulation (headerPlan rowPlan : Plan)
    (a b : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg)
    (step : (FinalCNFMachine.Program.machine headerPlan rowPlan).step a = some b) :
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan a) =
      some (embeddedCfg headerPlan rowPlan b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (FinalCNFMachine.Program.program headerPlan rowPlan label)
          state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
          (FinalCNFMachine.Program.program headerPlan rowPlan label)) state tapes) = _
      erw [stepAux_redirect]
      rfl

@[simp] theorem embedded_init (headerPlan rowPlan : Plan) (input : List Bool) :
    embeddedCfg headerPlan rowPlan (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input) =
      initList (completedMachine headerPlan rowPlan) input := rfl

theorem finalTapes_eq (base : Tape → List Bool) :
    MachineDrainMany.finalTapes chosen base = MachineDrainMany.haltTapes .output (base .output) := by
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  simp only [mem_chosen]
  by_cases h : tape = .output
  · subst tape
    simp [MachineDrainMany.haltTapes]
  · simp [MachineDrainMany.haltTapes, h]

theorem haltList_eq (headerPlan rowPlan : Plan) (output : List Bool) :
    haltList (completedMachine headerPlan rowPlan) output =
      ⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.haltTapes .output output⟩ := by
  congr 1

/-- Actual drains followed by a real state-reset instruction reach canonical halt. -/
def cleanupExecution (headerPlan rowPlan : Plan) (state : State Unit) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩
      (some (haltList (completedMachine headerPlan rowPlan) (base .output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine headerPlan rowPlan).Cfg :=
    ⟨some (resetLabel headerPlan rowPlan),
      (state.1, MachineDrainMany.finalRegister chosen state.2),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) (completedProgram headerPlan rowPlan)
      (fun _ => rfl) base state.1 state.2
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      after (some (haltList (completedMachine headerPlan rowPlan) (base .output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.finalTapes chosen base⟩ : (completedMachine headerPlan rowPlan).Cfg) =
          some (haltList (completedMachine headerPlan rowPlan) (base .output))
      erw [finalTapes_eq, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

/-- The extra cost is bounded from the actual raw execution, independently of
the contents of its dirty private tapes and finite state. -/
def outputsInTime (headerPlan rowPlan : Plan) (input output : List Bool)
    (state : State Unit) (base : Tape → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input)
      (some ⟨none, state, base⟩) budget)
    (correctOutput : base .output = output) :
    TM2OutputsInTime (completedMachine headerPlan rowPlan) input (some output)
      (budget + 12 * (input.length + budget *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1) := by
  let lifted := liftExecutionInTime
    (FinalCNFMachine.Program.machine headerPlan rowPlan).step
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan)
    (step_simulation headerPlan rowPlan) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution headerPlan rowPlan state base)
  have stackBound : ∀ tape, (base tape).length ≤ input.length + budget *
      Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) := by
    intro tape
    have h := Runtime.executionSizeBound
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (fun cfg => (cfg.stk tape).length)
      (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan))
      (Runtime.stepStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) tape) raw
    exact h.trans (Nat.add_le_add_right
      (Runtime.initialStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) input tape) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [chosen_length] at cleanupBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

end MaxCutGames.Foundations.Complexity.FinalCNFCleanup

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP

theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

/-- A concrete finite machine computes the complete CNF serialization from
the exact unary graph-table serialization, with a proved polynomial bound. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output where
  tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))
  outputsFun table := by
    change TM2OutputsInTime (FinalCNFCleanup.completedMachine headerPlan rowPlan)
      ((GraphTables.tableBits table).map id)
      (some ((formulaBits (FinalTableFormula.output table)).map id))
      ((finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))).eval
        (GraphTables.tableBits table).length)
    have hi := @List.map_id
      ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
        (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀) (GraphTables.tableBits table)
    have ho := @List.map_id
      ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
        (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
      (formulaBits (FinalTableFormula.output table))
    rw [hi, ho, finalTimePolynomial_eval]
    let raw := rawRun rowPlan table
    let bounded : StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
        (initList (machine headerPlan rowPlan) (GraphTables.tableBits table))
        (some ⟨none, ((raw.finalAmbient, ()), none), raw.finalTapes⟩)
        (phaseTimePolynomial.eval (GraphTables.tableBits table).length) := {
      toEvalsTo := raw.execution.toEvalsTo
      steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
    have correct : raw.finalTapes .output = formulaBits (FinalTableFormula.output table) :=
      raw.output.trans (emittedBytes_eq_formulaBits table)
    have run := FinalCNFCleanup.outputsInTime headerPlan rowPlan
      (GraphTables.tableBits table) (formulaBits (FinalTableFormula.output table))
      ((raw.finalAmbient, ()), none) raw.finalTapes
      (phaseTimePolynomial.eval (GraphTables.tableBits table).length) bounded correct
    exact run

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCanonicalOutput
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

/-- The cleanup path consists of actual drains and one physical state reset. -/
def cleanupExecution (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (state : σ)
    (register : Option Bool) (base : K → List Bool) :
    StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩
      (some (haltList (completedMachine P chosen) (base P.output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine P chosen).Cfg :=
    ⟨some (resetLabel chosen), (state, MachineDrainMany.finalRegister chosen register),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) (completedProgram P chosen) (fun _ => rfl) base state register
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine P chosen).step
      after (some (haltList (completedMachine P chosen) (base P.output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (P.initial, none), MachineDrainMany.finalTapes chosen base⟩ :
          (completedMachine P chosen).Cfg) =
        some (haltList (completedMachine P chosen) (base P.output))
      erw [finalTapes_eq P chosen complete, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

/-- No assumption about cleanup execution or clean raw work tapes is required. -/
def outputsInTime (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (input output : List Bool) (state : σ) (base : K → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime (sourceMachine P).step
      (initList (sourceMachine P) input) (some ⟨none, state, base⟩) budget)
    (correctOutput : base P.output = output) :
    TM2OutputsInTime (completedMachine P chosen) input (some output)
      (budget + chosen.length *
        (input.length + budget * Runtime.programPushBound (sourceMachine P) + 1) + 1) := by
  let lifted := liftExecutionInTime (sourceMachine P).step
    (completedMachine P chosen).step (embeddedCfg P chosen) (step_simulation P chosen) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution P chosen complete state none base)
  have stackBound : ∀ k, (base k).length ≤
      input.length + budget * Runtime.programPushBound (sourceMachine P) := by
    intro k
    have h := Runtime.executionSizeBound (sourceMachine P).step
      (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (sourceMachine P))
      (Runtime.stepStackLength (sourceMachine P) k) raw
    exact h.trans (Nat.add_le_add_right (Runtime.initialStackLength (sourceMachine P) input k) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

/-- A polynomial raw run becomes a full canonical-output computation certificate. -/
noncomputable def computableInPolyTime {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    TM2ComputableInPolyTime encodeIn encodeOut f where
  tm := completedMachine P chosen
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := completedTime P chosen rawTime
  outputsFun a := by
    change TM2OutputsInTime (completedMachine P chosen) ((encodeIn a).map id)
      (some ((encodeOut (f a)).map id)) ((completedTime P chosen rawTime).eval _)
    have hi := @List.map_id
      ((completedMachine P chosen).Γ (completedMachine P chosen).k₀) (encodeIn a)
    have ho := @List.map_id
      ((completedMachine P chosen).Γ (completedMachine P chosen).k₁) (encodeOut (f a))
    erw [hi, ho, completedTime_eval]
    exact outputsInTime P chosen complete _ _ (run a).state (run a).tapes _
      (run a).execution (run a).output_eq

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

end MaxCutGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderRowFrames
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions. These are data identities and
size bounds, not assumed machine executions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

namespace RowData

variable {v d : Nat} (r : RowData v d)

theorem rows_le_tableLength : v * degree d ≤ r.tableLength := by
  simp only [tableLength, encodeWords_length, rotationWords_length]
  omega

theorem query1_le_tableLength : r.query1 ≤ r.tableLength := by
  rw [query1_eq_firstRow]
  exact r.firstRow.isLt.le.trans r.rows_le_tableLength

theorem query2_le_tableLength : r.query2 ≤ r.tableLength := by
  rw [query2_eq_secondRow]
  exact r.secondRow.isLt.le.trans r.rows_le_tableLength

theorem firstValue_le_tableLength : r.firstValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.firstRow).isLt.le.trans r.rows_le_tableLength

theorem secondValue_le_tableLength : r.secondValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.secondRow).isLt.le.trans r.rows_le_tableLength

theorem inputVertex_le_tableLength : r.inputVertex.val ≤ r.tableLength := by
  have hq : 1 ≤ degree d := Nat.zero_lt_of_lt r.inputPort.isLt
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  exact r.inputVertex.isLt.le.trans (hv.trans r.rows_le_tableLength)

theorem firstVertex_le_tableLength : r.firstVertex.val ≤ r.tableLength := by
  rw [← firstValue_div_degree]
  exact (Nat.div_le_self r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondVertex_le_tableLength : r.secondVertex.val ≤ r.tableLength := by
  rw [← secondValue_div_degree]
  exact (Nat.div_le_self r.secondValue (degree d)).trans r.secondValue_le_tableLength

theorem firstReturn_le_tableLength : r.firstReturn.val ≤ r.tableLength := by
  rw [← firstValue_mod_degree]
  exact (Nat.mod_le r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondReturn_le_tableLength : r.secondReturn.val ≤ r.tableLength := by
  rw [← secondValue_mod_degree]
  exact (Nat.mod_le r.secondValue (degree d)).trans r.secondValue_le_tableLength

end RowData

variable {v d : Nat}

/-! Direct input facts for the individual checked phase traces. -/

theorem cleanupSteps_le_tableLength (r : RowData v d) (output : List Bool) :
    cleanupSteps id (frame11 r output) ≤ 6 * (r.tableLength + 1) + 6 := by
  have h1 := r.firstVertex_le_tableLength
  have h2 := r.secondVertex_le_tableLength
  have h3 := r.firstReturn_le_tableLength
  have h4 := r.secondReturn_le_tableLength
  simp only [cleanupSteps, frame11_eq, id_eq, frameContents, encodeWord_length]
  omega

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

theorem rowSteps_le {v d : Nat} (r : RowData v d) (output : List Bool) :
    rowSteps r output ≤ 80 * (r.tableLength + 1) := by
  have lookup1 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.firstRow.val r.firstValue (rotationWords_getElem? r.oldTable r.firstRow)
  have lookup2 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.secondRow.val r.secondValue (rotationWords_getElem? r.oldTable r.secondRow)
  have h0 := r.inputVertex_le_tableLength
  have h1 := r.query1_le_tableLength
  have h2 := r.firstValue_le_tableLength
  have h3 := r.firstVertex_le_tableLength
  have h4 := r.query2_le_tableLength
  have h5 := r.secondValue_le_tableLength
  have h6 := r.secondVertex_le_tableLength
  have clean := cleanupSteps_le_tableLength r output
  change _ ≤ 6 * r.tableLength + 4 at lookup1 lookup2
  simp only [rowSteps, emitSteps]
  omega

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

variable [Fintype ρ]

theorem afterRow_last_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H)
      ⟨some (.inr .afterRow), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        boundaryTapes (vertex + 1) remaining oldTable output countSuffix result⟩ := by
  have input : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .inputVertex) = encodeWord vertex := rfl
  have h := afterRow_lastStep positive H
    (boundaryTapes vertex remaining oldTable output countSuffix result) state last
  simp only [input] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), resetPositionState positive state, tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (boundaryTapes_increment_vertex vertex remaining oldTable output countSuffix result))

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem tableRowData_frame0 {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.frame0 (tableRowData G H vertex position) output =
      rowTapes vertex.val (encodeWords (rotationWords G)) output := by
  funext tape
  cases tape <;> rfl

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev Alphabet (_ : Tape) := Bool

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

namespace MaxCutGames.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

@[simp] theorem resultTapes_work (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 1 = rowsBits := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_scratch (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 2 = [] := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_vertices (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 3 = encodeWord n := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_darts (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 4 = encodeWord m := by simp [resultTapes, tapes]

end MaxCutGames.Foundations.Complexity.MachineTableSplit

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

/-! Exact table-codec endpoint of the polynomial padding-row routine.
The caller supplies the physical unary counters and copied old-row buffer
with the updated headers. This theorem executes every added row and proves
that the resulting output is exactly the existing full table encoding. -/

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace MaxCutGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def loopTapes (d : Nat) (input : List Bool) (n m left v : Nat)
    (source output : List Bool) : Tape → List Bool :=
  frame input source output (encodeWord n) (encodeWord m) (encodeWord left)
    (encodeWord v) (encodeWord (2 * d * v))

end MaxCutGames.Foundations.Complexity.MachineLazyTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/

/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLogCounter

open Turing

theorem stripTrace (n : Nat) (scratch output : List Bool) (state : State) :
    next^[n + 1] (some (configuration (some 1) state (encodeWord n) scratch output)) =
      some (configuration (some 4) initialState [] (List.replicate n true ++ scratch) output) := by
  induction n generalizing scratch state with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, Nat.zero_add,
      Function.iterate_one, next, MachineComposition.advance_some] using
      stripStep_false scratch output state
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change next^[n + 1]
      (machine.step (configuration (some 1) state (true :: encodeWord n) scratch output)) = _
    rw [stripStep_true, ih]
    congr 2
    simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

theorem machineTrace (n : Nat) :
    next^[totalTime n] (some (initList machine (encodeWord n))) =
      some (haltList machine (encodeWord (n.log2 + 1))) := by
  rw [initList_eq, haltList_eq]
  rw [show totalTime n = (coreTime n + (n + 1) + (n + 1)) + 1 by
    unfold totalTime; omega, Function.iterate_succ_apply]
  change next^[coreTime n + (n + 1) + (n + 1)]
    (machine.step (configuration (some 0) initialState (encodeWord n) [] [])) = _
  rw [initialStep, Function.iterate_add_apply, stripTrace]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply]
  dsimp only [initialState]
  rw [restoreTrace n [false] false, coreTrace, increments_false]
  rfl

def outputsInTime (n : Nat) :
    TM2OutputsInTime machine (encodeWord n) (some (encodeWord (n.log2 + 1))) (8 * n + 4) where
  steps := totalTime n
  evals_in_steps := machineTrace n
  steps_le_m := totalTime_bound n

end MaxCutGames.Foundations.Complexity.MachineLogCounter

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

end MaxCutGames.Foundations.Complexity.GraphCounterModel

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

theorem headerStep_zero (again next : Label)
    (atHeader : program again = readHeader again next)
    (suffix archive : List Bool) (sum : Nat)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register), startMemory (encodeWord 0 ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord sum)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_zero, List.nil_append, List.singleton_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  rw [startMemory_input_update]

theorem headerStep_succ (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register),
        startMemory (encodeWord (n + 1) ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some again, (state, some true),
        startMemory (encodeWord n ++ suffix) archive (encodeWord (sum + 1))⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.cond_true]
  rw [startMemory_input_update, startMemory_sum_update]
  rfl

theorem headerTrace (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (state, register),
        startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩) =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩ := by
  induction n generalizing sum register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
        headerStep_zero again next atHeader suffix archive sum state register
  | succ n ih =>
      rw [Function.iterate_succ_apply, MachineComposition.advance_some]
      rw [headerStep_succ again next atHeader n sum suffix archive state register]
      simpa only [Nat.add_assoc, Nat.add_comm 1 sum] using ih (sum + 1) (some true)

def headerInTime (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (state, register), startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩
      (some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := headerTrace again next atHeader n sum suffix archive state register
  steps_le_m := le_rfl

theorem clockInitialMemory (word rest : List Bool) (sum : Nat) :
    clockConfiguration (startExtra rest word) none
      (initList MachineLogCounter.machine (encodeWord sum)) =
      ⟨some (.inl 0), initialState, startMemory rest word (encodeWord sum)⟩ := by
  have ht : clockTapes (initList MachineLogCounter.machine (encodeWord sum)).stk
      (startExtra rest word) = startMemory rest word (encodeWord sum) := by
    funext tape
    cases tape with
    | inl k => fin_cases k <;> rfl
    | inr k => rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- Exact handoff from the genuine machine input to the actual logarithm
machine, with the original graph word protected in the archive. -/
def startInTime (n m : Nat) (rest : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (encodeWords [n, m] ++ rest))
      (some (clockConfiguration (startExtra rest (encodeWords [n, m] ++ rest)) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * ((encodeWords [n, m] ++ rest).length + 1) + 1 + (n + 1) + (m + 1)) := by
  let word := encodeWords [n, m] ++ rest
  let b₀ := startMemory word [] []
  let b₁ := startMemory word word []
  let b₂ := startMemory word word (encodeWord 0)
  have hc : Function.update b₀ (.inr .archive) (b₀ (.inr .input) ++ b₀ (.inr .archive)) = b₁ := by
    funext tape
    cases tape with
    | inl k => simp [b₀, b₁, startMemory]
    | inr k => cases k <;> simp [b₀, b₁, startMemory, startExtra]
  let copy := MachineCopy.copyInTime (.inr ExtraTape.input) (.inr ExtraTape.archive)
    (.inr ExtraTape.scratch) (by decide) (by decide) (by decide) false
    (.inr ExtraLabel.copyFirst) (.inr ExtraLabel.copySecond) (some (.inr ExtraLabel.seed))
    program rfl rfl b₀ rfl MachineLogCounter.initialState none
  have copy' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .copyFirst), initialState, b₀⟩
      (some ⟨some (.inr .seed), initialState, b₁⟩) (2 * (word.length + 1)) := by
    have h := copy
    rw [hc] at h
    simpa only [initialState, show b₀ (.inr .input) = word from rfl] using h
  have seed : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .seed), initialState, b₁⟩
      (some ⟨some (.inr .headerFirst), initialState, b₂⟩) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (TM2.stepAux (program (.inr .seed)) initialState b₁) = _
    simp only [program, TM2.stepAux, b₁, startMemory]
    rw [startMemory_sum_update]
    rfl
  have first := headerInTime (.inr .headerFirst) (.inr .headerSecond) rfl
    n 0 (encodeWord m ++ rest) word MachineLogCounter.initialState none
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerFirst), initialState, b₂⟩
      (some ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩) (n + 1) := by
    simpa only [b₂, initialState, word, encodeWords, List.append_nil, List.append_assoc,
      Nat.add_zero] using first
  have second := headerInTime (.inr .headerSecond) (.inl 0) rfl
    m n rest word MachineLogCounter.initialState none
  have second' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩
      (some ⟨some (.inl 0), initialState, startMemory rest word (encodeWord (n + m))⟩)
      (m + 1) := by simpa only [initialState, Nat.add_comm m n] using second
  let p₀ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copy' seed
  let p₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ first'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₁ second'
  rw [initialMemory, clockInitialMemory]
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change p.steps ≤ 2 * (word.length + 1) + 1 + (n + 1) + (m + 1)
      omega
  }

end MaxCutGames.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_GraphCounterFinish
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawOutput (n m : Nat) (rest : List Bool) : List Bool :=
  encodeWord ((n + m).log2 + 1) ++ (encodeWords [n, m] ++ rest)

def rawInTime (n m : Nat) (rest : List Bool) :
    TM2OutputsInTime machine (encodeWords [n, m] ++ rest) (some (rawOutput n m rest))
      (20 * (encodeWords [n, m] ++ rest).length + 30) := by
  let original := encodeWords [n, m] ++ rest
  let start := startInTime n m rest
  let clock := clockInTime (extraTapes rest original) none (n + m)
  let finish := finishInTime (encodeWord ((n + m).log2 + 1)) rest original
  have start' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine original)
      (some (clockConfiguration (extraTapes rest original) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * (original.length + 1) + 1 + (n + 1) + (m + 1)) := start
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start' clock
  let total := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  refine { toEvalsTo := total.toEvalsTo, steps_le_m := ?_ }
  have bound := total.steps_le_m
  have hlog := Nat.log2_le_self (n + m)
  have hlength : original.length = n + m + 2 + rest.length := by
    simp only [original, List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  simp only [encodeWord_length] at bound
  change total.steps ≤ 20 * original.length + 30
  omega

def output (table : GraphTables.Table) : List Bool :=
  encodeWord (count table) ++ GraphTables.tableBits table

def rowsBits (table : GraphTables.Table) : List Bool :=
  encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)

theorem tableBits_decomposition (table : GraphTables.Table) :
    GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table :=
  encodeWords_append _ _

def outputsInTime (table : GraphTables.Table) :
    TM2OutputsInTime machine (GraphTables.tableBits table) (some (output table))
      (20 * (GraphTables.tableBits table).length + 30) := by
  have run := rawInTime table.vertices table.darts (rowsBits table)
  simpa only [rawOutput, output, count, tableBits_decomposition] using run

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits id output where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 30
  outputsFun table := by
    change TM2OutputsInTime machine ((GraphTables.tableBits table).map id)
      (some ((output table).map id))
      ((20 * Polynomial.X + 30 : Polynomial Nat).eval (GraphTables.tableBits table).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (GraphTables.tableBits table)
    have ho := @List.map_id (machine.Γ machine.k₁) (output table)
    rw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using outputsInTime table

end MaxCutGames.Foundations.Complexity.GraphCounterPrefix

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_GraphIterationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One polynomial bounds every actual intermediate encoding in the concrete
logarithmic graph iteration. The linear recurrence is on graph size. -/

namespace MaxCutGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

end MaxCutGames.Foundations.Complexity.GraphIterationBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OccurrenceTupleOrder
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

theorem selected_polynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) (M : Nat) :
    (MachineOutcomeRows.timePolynomial
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) b)).eval M =
        (rowPolynomial k T).eval M := by
  simp only [MachineOutcomeRows.timePolynomial, AddressOutcomeSpecs.selected_rows,
    List.map_map, Function.comp_def, AddressOutcomeSpecs.row_left_length,
    AddressOutcomeSpecs.row_right_length, Polynomial.eval_add, Polynomial.eval_one,
    eval_sum_constant_inline_AddressTupleBudget, FixedOutcomes.tableParams_length, rowPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem rows_budget_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    (MachineOutcomeRows.rowCosts (Slots k s d noiseCount)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base)).sum+1 ≤
        (rowPolynomial k T).eval (magnitude k s d (SourceEncoding.inputBits F).length) := by
  have h := MachineOutcomeRows.phaseCost_le_timePolynomial (Slots k s d noiseCount)
    (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
    (loaded F tuple base) _ _
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (magnitude k s d (SourceEncoding.inputBits F).length)
    (AddressTupleLoaded.loaded_clean F tuple base clean)
    (loaded_fields_le_magnitude F tuple base ready)
    (radix_le_magnitude F k s d) (capacity_le_magnitude F k s d)
    (selected_values_bound F tuple T)
  simpa only [selected_polynomial_eval] using h

theorem timePolynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) (L : Nat) :
    (timePolynomial k T).eval L =
      (k*(10*L+20)+1)+1+(rowPolynomial k T).eval (magnitude k s d L)+4*k*(L+2)+1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, magnitudePolynomial_eval]

/-- Uniform bound for the actual tuple body, with all canonical values instantiated. -/
theorem budget_le_timePolynomial (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    AddressTupleBody.budget (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ≤
        (timePolynomial k T).eval (SourceEncoding.inputBits F).length := by
  have rowsBound := rows_budget_le F tuple T base ready clean
  have cleanupBound := cleanup_budget_le (AddressOutcomeSpecs.rows k T)
    (CanonicalAddress.base F.«variables» F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d)
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ready
  rw [AddressTupleBody.budget, timePolynomial_eval]
  omega

end MaxCutGames.Integration.AddressTupleBudget

namespace MaxCutGames.Integration.AddressTuplePolynomial

open Turing Reduction Foundations.Complexity
open AddressTupleBody AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : AddressTupleBody.Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : AddressTupleBody.Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀ l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : AddressTupleBody.Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have actual := AddressTupleBody.run_actual T labels exit P atLabels F tuple base
    ready clean oldRhs hB hC
  exact {
    steps := actual.steps
    evals_in_steps := actual.evals_in_steps
    steps_le_m := actual.steps_le_m.trans
      (AddressTupleBudget.budget_le_timePolynomial F tuple T base ready clean)
  }

end MaxCutGames.Integration.AddressTuplePolynomial

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
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
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

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

attribute [local instance] OAI.MaxCutGames.Explicit.ProductPaddedOutput.instNonemptyFinLengthConstraintVerticesConstraints
theorem side_left (t : ℕ) (ht : 0 < t) (x : Fin t → Left H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inl x)) = false := by
  simp only [side, vertices]
  change presentation.side
    (finFunctionFinEquiv.symm (finFunctionFinEquiv (fun i => (x i).val)) ⟨0, ht⟩) = false
  rw [Equiv.symm_apply_apply]
  exact (x ⟨0, ht⟩).property

theorem side_right (t : ℕ) (ht : 0 < t) (y : Fin t → Right H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inr y)) = true := by
  simp only [side, vertices]
  change presentation.side
    (finFunctionFinEquiv.symm (finFunctionFinEquiv (fun i => (y i).val)) ⟨0, ht⟩) = true
  rw [Equiv.symm_apply_apply]
  exact (y ⟨0, ht⟩).property

def simpleBipartite (t : ℕ) (ht : 0 < t) : SimpleBipartite (output H presentation t ht) :=
  Embedded.simpleBipartite _ _ _ _ (side H presentation t ht)
    (side_left H presentation t ht) (side_right H presentation t ht)

noncomputable section

attribute [local instance] OAI.MaxCutGames.Explicit.ProductPaddedOutput.instNonemptyFinLengthConstraintVerticesConstraints
theorem output_value_eq_repetition [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) :
    Integration.InstanceValue.value (output H presentation t ht) =
      (presentation.toBipartiteGame.toGame.repetition t).value := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  let : Nonempty (Fin (q ^ t)) :=
    ⟨finFunctionFinEquiv (fun _ : Fin t => Classical.choice inferInstance)⟩
  rw [output, Embedded.value, ← BipartiteGame.toGame_value, graph,
    BipartiteGame.relabel_value, BipartiteGame.product_value_eq_repetition]

theorem output_completeness [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) {error : ℝ}
    (hcomplete : 1 - error ≤ Integration.InstanceValue.value H) :
    1 - (t : ℝ) * error ≤ Integration.InstanceValue.value (output H presentation t ht) := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition, ← BipartiteGame.product_value_eq_repetition]
  exact presentation.toBipartiteGame.product_completeness t
    (by simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hcomplete)

end

end MaxCutGames.Explicit.ProductPaddedOutput

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionTableRead
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

/-!
One whole occurrence iteration of the actual subdivision controller.
The proved trace includes both endpoint loads, the dynamic full-table reader,
the four-row template, all three local drains, and private-index increments.
-/

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

/-! Complete physical occurrence traversal of the subdivision program. -/

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

namespace MaxCutGames.Explicit.MachineSubdivisionFinish

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineSubdivisionProgram

noncomputable def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (q := q)) none (program q) (fun _ => rfl)
    base outputEmpty ((), ()) none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q)
    input (prefixTime + 1) prefixRun clearKeys Tape.accumulator Tape.output
    accumulator_not_mem_clearKeys output_not_mem_clearKeys covers base outputEmpty
    (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end MaxCutGames.Explicit.MachineSubdivisionFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionCorrespondence
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual streamed bytes coincide with the numbered semantic subdivision.
The controller copies the last table unchanged, so its input contract explicitly
requires involutive tables; binary translations satisfy this condition. -/

/-! The complete finite subdivision machine, including its polynomial runtime
in the actual serialized input length and exact full-table output. -/

namespace MaxCutGames.Explicit.MachineSubdivisionRuntime

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame
open MachineSubdivisionCorrespondence

noncomputable section

/-- Literal initialization to literal clean halting configuration, with exact
semantic subdivision output. No execution or runtime premise is assumed. -/
def fullRunInTime {q : Nat} (H : Instance q) (involutive : Involutive H) :
    TM2OutputsInTime (machine q) (gameBits H)
      (some (gameBits (SubdivisionTarget.subdivide H)))
      ((timePolynomial q).eval (gameBits H).length) := by
  have run := MachineSubdivisionFinish.completePrefix q (gameBits H) (prefixPolynomial q)
    (finalTapes H) (prefixInTime H) (final_outputEmpty H)
  simpa only [final_accumulator H involutive, List.reverse_reverse, timePolynomial] using run

/-- The input subtype records the mathematical involution property, while the
same finite transition program is used for every instance of the fixed alphabet. -/
def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime
      (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      gameBits (fun H => SubdivisionTarget.subdivide H.val) where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun H := by
    change TM2OutputsInTime (machine q) ((gameBits H.val).map id)
      (some ((gameBits (SubdivisionTarget.subdivide H.val)).map id))
      ((timePolynomial q).eval (gameBits H.val).length)
    have hi := @List.map_id ((machine q).Γ (machine q).k₀) (gameBits H.val)
    have ho := @List.map_id ((machine q).Γ (machine q).k₁)
      (gameBits (SubdivisionTarget.subdivide H.val))
    erw [hi, ho]
    exact fullRunInTime H.val H.property

theorem workAlphabetFinite (q : Nat) (tape : (computableInPolyTime q).tm.K) :
    Finite ((computableInPolyTime q).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end MaxCutGames.Explicit.MachineSubdivisionRuntime

namespace MaxCutGames.Explicit.MachineSubdivisionCompose

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionCorrespondence

noncomputable section

variable {α : Type} {q : Nat} {encode : α → List Bool} {f : α → Instance q}

def computableInPolyTime (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  MachineSequential.composeBits (f := certifiedOutput involutive)
    (g := fun H : {H : Instance q // Involutive H} => SubdivisionTarget.subdivide H.val)
    (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q)

theorem finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a))
    (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime upstream involutive).tm := by
  exact MachineFiniteAlphabet.composeBits (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q) finite
    (MachineSubdivisionRuntime.workAlphabetFinite q)

/-- Binary-translation producers discharge the only table-law condition. -/
def translationComputableInPolyTime {s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s)
    (upstream : TM2ComputableInPolyTime encode gameBits f)
    (translations : ∀ a, Integration.TranslationTarget.IsTranslationInstance coordinates (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  computableInPolyTime upstream (fun a => translations_involutive coordinates (f a) (translations a))

end
end MaxCutGames.Explicit.MachineSubdivisionCompose

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ProductSoundness
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The final graph product inherits the alphabet-independent repetition estimate
through its proved uniform occurrence law and arbitrary-local-strategy bridge.
The only input soundness premise is the base graph's actual finite maximum.
-/

namespace MaxCutGames.Explicit.ProductPaddedOutput

open MaxCutGames.Foundations
open Target
open MachineOutputContract

noncomputable section

variable {q : ℕ} [Nonempty (Fin q)]

/-- Soundness for the actual globally numbered, fully tabulated output. -/
theorem output_soundness_rate (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤
      (1 - (1 : ℝ) / 10240000) ^ t := by
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition]
  apply MaxCutGames.Repetition.final_repetition_value
    presentation.toBipartiteGame.toGame presentation.toBipartiteGame.toGame_isProjection
  simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hvalue

theorem output_soundness (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤ δ :=
  (output_soundness_rate H presentation t ht hvalue).trans hcount

end
end MaxCutGames.Explicit.ProductPaddedOutput
end

/-!
The concrete final composition, once the matrix reduction has been proved.
This constructor copies the actual occurrence list, subdivides every occurrence
into four edges, and runs the full tuple-product machine. Its hypotheses are
the matrix reduction's actual value bounds and finite-machine computation.
It is an intermediate composition theorem, not the unconditional v2 endpoint.
-/

namespace MaxCutGames.FinishReduction

open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Integration
open Explicit

noncomputable section

/-- Compose the proved matrix reduction with the explicit three-stage finish.
All parameters, machines, alphabets, and time polynomials precede the input.
The original raw binary input codec is retained by sequential composition. -/
def of_matrix_reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    {q s : ℕ} (hq : 2 ≤ q) (hs : 1 ≤ s)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (matrix : List Bool → Instance q)
    (translations : ∀ input, TranslationTarget.IsTranslationInstance coordinates (matrix input))
    (computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      gameBits matrix)
    (finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm)
    (d : ℚ) (hd : d ≤ P.epsilon0 / P.repetitions)
    (complete : ∀ input, BinaryLanguage.language input →
      1 - (d : ℝ) ≤ InstanceValue.value (matrix input))
    (sound : ∀ input, ¬BinaryLanguage.language input →
      InstanceValue.value (matrix input) ≤ 99 / 100) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hqpos : 0 < q := by omega
  have hC : 0 < P.copies := by have h := P.copies_large; omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  let rounded := fun input => UniformTarget.construct P.copies hC (matrix input)
  have roundedTranslations : ∀ input,
      TranslationTarget.IsTranslationInstance coordinates (rounded input) := fun input =>
    UniformTarget.translations P.copies hC (matrix input) coordinates (translations input)
  let roundedMachine := MachineSequential.composeBits
    (f := matrix) (g := UniformTarget.construct P.copies hC) computation
    (MachineUniformRun.computation (q := q) P.copies hC)
  have roundedFinite : MachineFiniteAlphabet.FiniteAlphabet roundedMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := matrix) (g := UniformTarget.construct P.copies hC) computation
      (MachineUniformRun.computation (q := q) P.copies hC) finiteAlphabet
      (MachineUniformRun.finiteAlphabet (q := q) P.copies hC)
  let base := fun input => SubdivisionTarget.subdivide (rounded input)
  let basePresentation := fun input => SubdivisionTarget.simpleBipartite (rounded input)
  let baseMachine := MachineSubdivisionCompose.translationComputableInPolyTime
    coordinates roundedMachine roundedTranslations
  have baseFinite : MachineFiniteAlphabet.FiniteAlphabet baseMachine.tm :=
    MachineSubdivisionCompose.finiteAlphabet roundedMachine
      (fun input => MachineSubdivisionCorrespondence.translations_involutive
        coordinates (rounded input) (roundedTranslations input)) roundedFinite
  let output := fun input => ProductPaddedOutput.output (base input)
    (basePresentation input) P.repetitions P.repetitions_pos
  let outputMachine := MachineProductRuntime.compose baseMachine basePresentation
    P.repetitions P.repetitions_pos
  have hqout : 2 ≤ q ^ P.repetitions :=
    hq.trans (Nat.le_self_pow P.repetitions_pos.ne' q)
  have hqoutpos : 0 < q ^ P.repetitions := by omega
  have baseValue (input : List Bool) :
      InstanceValue.value (base input) =
        1 - (1 - InstanceValue.value (matrix input)) / 4 := by
    dsimp [base, rounded]
    rw [SubdivisionTarget.value_eq _ hqpos,
      UniformTarget.value P.copies hC (matrix input) hqpos]
  have hτ : (0 : ℝ) < (P.pStar : ℝ) := by exact_mod_cast P.pStar_pos
  have hτsmall : (P.pStar : ℝ) ≤ 1 / 200 := by
    simpa only [ParameterSelection.OuterParameters.pStar, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one]
      using ((Rat.cast_le (K := ℝ)).mpr P.reciprocal_small)
  have hτbudget : (P.pStar : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast P.reciprocal_budget
  have hdbudget : (d : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast hd
  have hε0 : (0 : ℝ) ≤ (P.epsilon0 : ℝ) := by
    exact_mod_cast P.epsilon0_pos.le
  have roundingError (input : List Bool) :
      |InstanceValue.value (base input) -
        (1 - (1 - InstanceValue.value (matrix input)) / 4)| ≤ (P.pStar : ℝ) / 4 := by
    rw [baseValue input, sub_self, abs_zero]
    positivity
  refine {
    alphabet := q ^ P.repetitions
    alphabetAtLeastTwo := hqout
    dimension := s * P.repetitions
    dimensionPositive := by
      have hpos := Nat.mul_pos (show 0 < s by omega) P.repetitions_pos
      omega
    coordinates := ProductPaddedOutput.finalCoordinates coordinates P.repetitions
    construct := output
    simpleBipartite := fun input => ProductPaddedOutput.simpleBipartite
      (base input) (basePresentation input) P.repetitions P.repetitions_pos
    translations := fun input => ProductPaddedOutput.output_translations
      (base input) (basePresentation input) coordinates
      (SubdivisionTarget.subdivide_translation coordinates (rounded input)
        (roundedTranslations input)) P.repetitions P.repetitions_pos
    computation := outputMachine
    finiteAlphabet := MachineProductRuntime.compose_finiteAlphabet
      baseMachine basePresentation P.repetitions P.repetitions_pos baseFinite
    completeness := ?_
    soundness := ?_
  }
  · intro input yes
    apply (InstanceValue.exists_rate_ge_iff (output input) hqoutpos (1 - ε)).mpr
    have hbase := FinishBounds.subdivision_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (complete input yes) (roundingError input)
    have hproduct := ProductPaddedOutput.output_completeness (base input)
      (basePresentation input) P.repetitions P.repetitions_pos
      (error := 1 - InstanceValue.value (base input)) (by linarith)
    exact FinishBounds.final_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (P.epsilon0 : ℝ) ε P.repetitions P.repetitions_pos hbase hproduct
      hdbudget hτbudget hε0 P.epsilon0_le
  · intro input no
    apply (InstanceValue.forall_rate_le_iff (output input) hqoutpos δ).mpr
    have hbase := FinishBounds.subdivision_soundness _ _ (P.pStar : ℝ)
      (sound input no) hτsmall (roundingError input)
    exact (ProductPaddedOutput.output_soundness (base input) (basePresentation input)
      P.repetitions P.repetitions_pos P.soundness_rate hbase).trans P.delta0_le

end
end MaxCutGames.FinishReduction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineInitial
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineInitial

open Turing MaxCutGames.Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

/-- Actual two-phase initialization from the concrete machine input. -/
def inTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval
        (SourceEncoding.inputBits F).length + k * (2 * (SourceEncoding.inputBits F).length + 6) + 1) := by
  have header := MachineAddressHeaders.inPolynomialTime
    (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.headerLabels k T) (some (AddressMachineProgram.initializeStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atHeader k T)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) F
    (AddressMachineProgram.inputTapes_source k T _) (input_headerClean k T F)
    (AddressMachineSpace.initialState k).1.1 none
  have digits := MachineOdometerInit.initializeInTime
    (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    (AddressMachineProgram.initializeLabels k T) (some (AddressMachineProgram.bodyStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atInitialize k T)
    F.equations.length (List.length_pos_iff.mpr F.nonempty) (afterHeaders k T F)
    (afterHeaders_occurrences k T F) (afterHeaders_current k T F)
    (afterHeaders_remaining k T F) (afterHeaders_copyScratch k T F)
    (AddressMachineSpace.initialState k).1
  have run := StateTransition.EvalsToInTime.trans (AddressMachineProgram.machine k T).step
    _ _ _ _ _ header digits
  refine { steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · rw [AddressMachineProgram.initList_eq]
    exact run.evals_in_steps
  · apply Nat.le_trans run.steps_le_m
    have hm := SourceEncoding.inputBits_length_ge_equations F
    have hmul := Nat.mul_le_mul_left k (show 2 * F.equations.length + 6 ≤
      2 * (SourceEncoding.inputBits F).length + 6 by omega)
    omega

def timePolynomial : Polynomial Nat :=
  MachineAddressHeaders.timePolynomial k s d T.vectors.length +
    Polynomial.C k * (Polynomial.C 2 * Polynomial.X + Polynomial.C 6) + Polynomial.C 1

theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N =
      (MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval N +
        k * (2 * N + 6) + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  rw [timePolynomial_eval]
  exact inTime k T F

end
end MaxCutGames.Reduction.AddressMachineInitial

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSingleOrbitProgram
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

/-! Exact streaming traces in the single-orbit postprocessor. -/

/-! Physical unary header conversion, with an exact TM2 transition count. -/

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

/-! The exact input/output codec of the one-orbit postprocessor. Doubling is
only an encoding adapter: no equality of game values under independent labels
on the two copies is asserted. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitCodec

open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

theorem gameBits_eq {q : Nat} (I : Instance q) :
    gameBits I = encodeWord I.vertices ++ encodeWord q ++
      encodeWord I.constraints.length ++ rowsBits I.constraints := by
  simp [gameBits, gameWords, encodeWords, rowsBits, List.append_assoc]

theorem doubled_gameBits_eq {q : Nat} (I : Instance q) :
    gameBits (doubleInstance I) = encodeWord (2 * I.vertices) ++ encodeWord q ++
      encodeWord I.constraints.length ++ doubledRowsBits I.constraints := by
  simp [gameBits, gameWords, doubleInstance, encodeWords, doubledRowsBits,
    List.flatMap_map, List.append_assoc]

theorem input_length_eq {q : Nat} (I : Instance q) :
    (gameBits (doubleInstance I)).length =
      2 * I.vertices + q + I.constraints.length + 3 +
        (doubledRowsBits I.constraints).length := by
  rw [doubled_gameBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem vertices_le_input_length {q : Nat} (I : Instance q) :
    I.vertices ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

theorem rows_le_input_length {q : Nat} (I : Instance q) :
    I.constraints.length ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

end MaxCutGames.Explicit.MachineSingleOrbitCodec

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitRows

open Turing MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitSubtract MachineSingleOrbitCodec

def rowCost {C q : Nat} (c : Constraint C q) : Nat :=
  (doubledRowBits c).length + C + 3

theorem rowTrace {C q : Nat} (c : Constraint C q)
    (suffix remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowCost c]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .guard none suffix (encodeWord C) [] remaining
        ((rowBits c).reverse ++ accumulator) output) := by
  let table := encodeWords (tableWords c.permutation)
  let afterSource := (encodeWord c.source.val).reverse ++ accumulator
  let afterTarget := (encodeWord c.target.val).reverse ++ afterSource
  have hs := copyFieldTrace (q := q) .source .subtract rfl c.source.val
    (encodeWord (C + c.target.val) ++ table ++ suffix)
    (encodeWord C) [] remaining accumulator output register
  have hd := removeOffsetTrace q C c.target.val (table ++ suffix)
    remaining afterSource output none
  have ht := copyFieldTrace (q := q) .target (.table 0) rfl c.target.val
    (table ++ suffix) (encodeWord C) [] remaining afterSource output none
  have hp := tableTrace (q := q) 0 (tableWords c.permutation)
    (by simp) suffix (encodeWord C) [] remaining afterTarget output none
  have hs' : (advance (TM2.step (program q)))^[c.source.val + 1]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .subtract none (encodeWord (C + c.target.val) ++ (table ++ suffix))
        (encodeWord C) [] remaining afterSource output) := by
    simpa only [doubledRowBits_eq, List.append_assoc, afterSource, table] using hs
  have hsd := joinTrace hs' hd
  have hsdt := joinTrace hsd ht
  have hall := joinTrace hsdt hp
  have hcost : (encodeWords (tableWords c.permutation)).length + 1 +
        (c.target.val + 1 + (2 * (C + 1) + (c.source.val + 1))) = rowCost c := by
    simp only [rowCost, doubledRowBits_eq, List.length_append, encodeWord_length]
    omega
  rw [hcost] at hall
  simpa only [rowBits_eq, List.reverse_append, List.append_assoc,
    afterTarget, afterSource, table] using hall

theorem guardStep_succ (q n : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord (n + 1)) accumulator output) =
      some (cfg .source none input capacity saved (encodeWord n) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

theorem guardStep_zero (q : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord 0) accumulator output) =
      some (cfg .finishStart none input capacity saved (encodeWord 0) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord]

def rowsCost {C q : Nat} (cs : List (Constraint C q)) : Nat :=
  (doubledRowsBits cs).length + (C + 4) * cs.length + 1

theorem rowsCost_cons {C q : Nat} (c : Constraint C q) (cs : List (Constraint C q)) :
    rowsCost (c :: cs) = rowsCost cs + rowCost c + 1 := by
  simp only [rowsCost, rowCost, doubledRowsBits_cons, List.length_append,
    List.length_cons, Nat.mul_add, Nat.mul_one]
  omega

/-- The actual counted loop visits every row once and preserves its order.
No complete-loop execution is supplied as an input hypothesis. -/
theorem rowsTrace {C q : Nat} (cs : List (Constraint C q))
    (suffix accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowsCost cs]
      (some (cfg .guard register (doubledRowsBits cs ++ suffix)
        (encodeWord C) [] (encodeWord cs.length) accumulator output)) =
      some (cfg .finishStart none suffix (encodeWord C) [] (encodeWord 0)
        ((rowsBits cs).reverse ++ accumulator) output) := by
  induction cs generalizing accumulator register with
  | nil =>
    simpa [rowsCost] using guardStep_zero q suffix (encodeWord C) [] accumulator output register
  | cons c cs ih =>
    have hg : (advance (TM2.step (program q)))^[1]
        (some (cfg .guard register (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] (encodeWord (c :: cs).length) accumulator output)) =
        some (cfg .source none (doubledRowBits c ++ (doubledRowsBits cs ++ suffix))
          (encodeWord C) [] (encodeWord cs.length) accumulator output) := by
      simpa only [Function.iterate_one, advance_some, List.length_cons,
        doubledRowsBits_cons, List.append_assoc] using
        guardStep_succ q cs.length (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] accumulator output register
    have hr := rowTrace c (doubledRowsBits cs ++ suffix) (encodeWord cs.length)
      accumulator output none
    have ht := ih ((rowBits c).reverse ++ accumulator) none
    have hall := joinTrace (joinTrace hg hr) ht
    have hcost : rowsCost cs + (rowCost c + 1) = rowsCost (c :: cs) := by
      rw [rowsCost_cons]
      omega
    rw [hcost] at hall
    simpa only [rowsBits_cons, List.reverse_append, List.append_assoc] using hall

end MaxCutGames.Explicit.MachineSingleOrbitRows

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitFinish

open Turing MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

noncomputable section

theorem haltList_eq (q : Nat) (bits : List Bool) : haltList (machine q) bits =
    ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  change (⟨none, initialState, (haltList (machine q) bits).stk⟩ : (machine q).Cfg) = _
  apply congrArg (fun base => (⟨none, initialState, base⟩ : (machine q).Cfg))
  funext tape
  cases tape <;> simp [haltList, machine, SourceRuntimeFinish.canonicalTapes] <;> rfl

/-- This helper consumes a proved prefix trace. The final runtime theorem
supplies that trace from the concrete header and complete row traversal. -/
def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys clearKeys_covers
    () Label.finish none (program q) (fun _ => rfl) base outputEmpty () none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q) input (prefixTime + 1)
    prefixRun clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys clearKeys_covers base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

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

def prefixCost {q : Nat} (I : Instance q) : Nat :=
  (gameBits (doubleInstance I)).length + (I.vertices + 4) * I.constraints.length + 2

/-- The complete prefix is obtained from the actual header and row traces. -/
theorem prefixTrace {q : Nat} (I : Instance q) :
    (advance (TM2.step (program q)))^[prefixCost I]
      (some (initList (machine q) (gameBits (doubleInstance I)))) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
  have hh := MachineSingleOrbitHeader.headerTrace q I.vertices I.constraints.length
    (doubledRowsBits I.constraints)
  have hr := rowsTrace I.constraints []
    (encodeWords [I.vertices, q, I.constraints.length]).reverse [] none
  have hbits : gameBits I =
      encodeWords [I.vertices, q, I.constraints.length] ++ rowsBits I.constraints := by
    simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc] using gameBits_eq I
  have hr' : (advance (TM2.step (program q)))^[rowsCost I.constraints]
      (some (cfg .guard none (doubledRowsBits I.constraints) (encodeWord I.vertices) []
        (encodeWord I.constraints.length)
        (encodeWords [I.vertices, q, I.constraints.length]).reverse [])) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
    simpa only [List.append_nil, cfg, finalTapes, hbits, List.reverse_append, initialState]
      using hr
  have run := joinTrace hh hr'
  have hcost : rowsCost I.constraints +
      (2 * I.vertices + q + I.constraints.length + 4) = prefixCost I := by
    rw [prefixCost, input_length_eq]
    unfold rowsCost
    omega
  rw [hcost] at run
  simpa only [doubled_gameBits_eq] using run

theorem prefixCost_le {q : Nat} (I : Instance q) :
    prefixCost I ≤ prefixPolynomial.eval (gameBits (doubleInstance I)).length := by
  have hC := vertices_le_input_length I
  have hm := rows_le_input_length I
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hC 4) hm
  simp only [prefixCost, prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

def prefixInTime {q : Nat} (I : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits (doubleInstance I)))
      (some ⟨some .finishStart, initialState, finalTapes I⟩)
      (prefixPolynomial.eval (gameBits (doubleInstance I)).length) where
  steps := prefixCost I
  evals_in_steps := prefixTrace I
  steps_le_m := prefixCost_le I

/-- Literal init-to-halt execution, with every non-output tape empty at halt. -/
def fullRunInTime {q : Nat} (I : Instance q) :
    TM2OutputsInTime (machine q) (gameBits (doubleInstance I))
      (some (gameBits I)) ((timePolynomial q).eval (gameBits (doubleInstance I)).length) := by
  let run := MachineSingleOrbitFinish.completePrefix q (gameBits (doubleInstance I))
    prefixPolynomial (finalTapes I) (prefixInTime I) rfl
  simpa only [finalTapes, tapes_accumulator, List.reverse_reverse, timePolynomial] using run

/-- A proved polynomial-time codec conversion, without an assumed time bound,
an output-size certificate, or an unbounded integer in finite machine state. -/
def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime (fun I : Instance q => gameBits (doubleInstance I)) gameBits id where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun I := by
    change TM2OutputsInTime (machine q) ((gameBits (doubleInstance I)).map id)
      (some ((gameBits I).map id))
      ((timePolynomial q).eval (gameBits (doubleInstance I)).length)
    have hi := @List.map_id ((machine q).Γ (machine q).k₀) (gameBits (doubleInstance I))
    have ho := @List.map_id ((machine q).Γ (machine q).k₁) (gameBits I)
    erw [hi, ho]
    exact fullRunInTime I

end

end MaxCutGames.Explicit.MachineSingleOrbitRuntime

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineLoop
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

/-- The local-body premise of the odometer theorem is derived from the actual
placed tuple-body implementation and its actual uniform budget theorem. -/
theorem bodyTrace (F : SourceEncoding.Input) :
    AddressOdometerSchedule.BodyTrace (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F)
      (bits k T F) ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  intro digits output
  let base := stateTapes k T F digits output
  have ready := stateTapes_ready k T F digits output
  have clean := stateTapes_clean k T F digits output
  have actual := AddressTuplePolynomial.run_actual T (AddressMachineProgram.bodyLabels k T) (some (AddressMachineProgram.next k T 0))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atBody k T) F
    (OccurrenceTupleOrder.readCoordinates digits) base ready clean (fun _ => false)
    (stateTapes_base k T F digits output) (stateTapes_capacity k T F digits output)
  refine ⟨actual.steps, actual.steps_le_m, ?_⟩
  have hemit : MachineAddressEdge.appended (AddressTupleBody.Slots k s d T.vectors.length)
      base (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
        (OccurrenceTupleOrder.readCoordinates digits)) =
      stateTapes k T F digits ((bits k T F digits).reverse ++ output) :=
    appended_stateTapes k T F digits output _
  exact actual.evals_in_steps.trans (congrArg
    (fun tapes => some (AddressOdometerSchedule.configuration
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 tapes)) hemit)

/-- Actual complete tuple traversal, before the final output reversal. -/
def traversal (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      (((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length + 2*k) *
        F.equations.length^k) := by
  have actual := AddressOdometerSchedule.traversalInTime (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
    (AddressMachineProgram.next k T) (AddressMachineProgram.resetAt k T) (AddressMachineSpace.initialState k).1
    (List.length_pos_iff.mpr F.nonempty)
    ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length)
    (AddressMachineInitial.initialized k T F) (bits k T F)
    (by
      intro i hi
      simp only [AddressMachineProgram.next_lt k T i hi, AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atCheck k T ⟨i,hi⟩)
    (by
      intro i hi
      simp only [AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atReset k T ⟨i,hi⟩)
    (bodyTrace k T F)
  have run := Classical.choice actual
  have hstart : AddressOdometerSchedule.initialConfiguration (m := F.equations.length) k
      (AddressMachineProgram.bodyStart k T) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F) =
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩ := by
    simp only [AddressOdometerSchedule.initialConfiguration, AddressOdometerSchedule.configuration,
      setDigits_initialized_zero, AddressMachineSpace.initialState]
  have hfinish : AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
      (AddressMachineInitial.initialized k T F) (bits k T F) =
      ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩ := by
    simp only [AddressOdometerSchedule.finalConfiguration, AddressOdometerSchedule.configuration, finalTapes,
      AddressMachineProgram.next_ge k T k (Nat.le_refl _), AddressMachineSpace.initialState]
  rw [hstart, hfinish] at run
  exact run

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have run := traversal k T F
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  rw [timePolynomial_eval]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (SourceEncoding.inputBits_length_ge_equations F) k)

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

namespace MaxCutGames.Reduction.MachineAddressGame

open Turing Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def prefixPolynomial : Polynomial Nat :=
  AddressMachineInitial.timePolynomial k T + AddressMachineLoop.timePolynomial k T

def timePolynomial : Polynomial Nat :=
  AddressMachineFinish.timePolynomial k T (prefixPolynomial k T)

/-- The complete actual prefix, with both initialization and every tuple body
supplied by their constructed finite programs. -/
def prefixInTime (input : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input))
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k,
        AddressMachineLoop.finalTapes k T input⟩)
      ((prefixPolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let initial := AddressMachineInitial.inPolynomialTime k T input
  let loop := AddressMachineLoop.inPolynomialTime k T input
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm] using run.steps_le_m

/-- Literal `initList` to literal `haltList`, including all private tape and
finite-state cleanup. This theorem has no runtime premise. -/
def fullRunInTime (input : SourceEncoding.Input) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input)
      (some (gameBits (output k T input)))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let run := AddressMachineFinish.completePrefix k T (SourceEncoding.inputBits input)
    (prefixPolynomial k T) (AddressMachineLoop.finalTapes k T input)
    (prefixInTime k T input) (AddressMachineLoop.final_outputEmpty k T input)
  simpa only [AddressMachineLoop.final_accumulator, List.reverse_reverse, output,
    Integration.AddressTupleBody.source, timePolynomial] using run

def computableInPolyTime :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) where
  tm := AddressMachineProgram.machine k T
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial k T
  outputsFun input := by
    change TM2OutputsInTime (AddressMachineProgram.machine k T)
      ((SourceEncoding.inputBits input).map id)
      (some ((gameBits (output k T input)).map id))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length)
    have hi := @List.map_id ((AddressMachineProgram.machine k T).Γ
      (AddressMachineProgram.machine k T).k₀) (SourceEncoding.inputBits input)
    have ho := @List.map_id ((AddressMachineProgram.machine k T).Γ
      (AddressMachineProgram.machine k T).k₁) (gameBits (output k T input))
    erw [hi, ho]
    exact fullRunInTime k T input

end
end MaxCutGames.Reduction.MachineAddressGame

/-!
The old addressed producer is reused only as a code generator. Its exact output
is the doubled codec of the new single-orbit game. The proved physical
postprocessor then yields the new game, with no premise about the value of the
legacy game and no legacy gadget or inverse theorem used.
-/

namespace MaxCutGames.Explicit.MachineSingleOrbitBridge

open Turing MaxCutGames.Reduction MaxCutGames.Foundations.Complexity
open ActualSource MachineSingleOrbitCodec

noncomputable section

/-- Reinterpret the existing producer using the proved exact codec equality. -/
def doubledComputableInPolyTime (k : Nat) {s d : Nat}
    (T : MaxCutGames.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits
      (fun I => gameBits (doubleInstance I)) (output k T) := by
  let old := MachineAddressGame.computableInPolyTime k T
  refine {
    tm := old.tm
    inputAlphabet := old.inputAlphabet
    outputAlphabet := old.outputAlphabet
    time := old.time
    outputsFun := ?_ }
  intro input
  rw [← old_output_eq_double k T input]
  exact old.outputsFun input

def computableInPolyTime (k : Nat) {s d : Nat}
    (T : MaxCutGames.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) :=
  MachineSequential.composeBits (f := output k T) (g := id) (doubledComputableInPolyTime k T)
    (MachineSingleOrbitRuntime.computableInPolyTime (2 ^ s))

end

end MaxCutGames.Explicit.MachineSingleOrbitBridge

namespace MaxCutGames.Explicit.MachineSingleOrbitBridge

theorem workAlphabetFinite (k : Nat) {s d : Nat}
    (T : MaxCutGames.Integration.NoiseTables.Table s d)
    (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) := by
  rcases tape with first | second
  · change Finite Bool
    infer_instance
  · rcases second with localTape | bridgeTape
    · change Finite Bool
      infer_instance
    · change Finite Bool
      infer_instance

end MaxCutGames.Explicit.MachineSingleOrbitBridge

end OAI
end


