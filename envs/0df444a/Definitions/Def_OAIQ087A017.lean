-- Prove2me | Definitions.Def_OAIQ087A017
-- name    : OAIQ087A017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:28:04.434826+00:00
-- url     : https://prove2.me/theorems/da1e8935-f6a9-406a-91eb-584fb5b1ffd5
-- title:
--   Definitions bundle OAIQ087A017 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 429 declarations of OpenAI's Lean: 172 definitions, 6 inductive types or structures and 251 theorems. The definitions and types are `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.Ready`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.afterDrainTable`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.afterDrainU`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.afterDrainV`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.afterRows`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.afterTable`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.afterU`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.afterV`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.bodyBudget`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.bodyResult`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.rowPayload`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.tableBits`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBodySpec.resultTapes`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBodySpec.rowBits`, `OAI.MaxCutGames.Explicit.MachineSubdivisionDynamicRows.rowBits`, `OAI.MaxCutGames.Explicit.MachineSubdivisionDynamicRows.rows`, `OAI.MaxCutGames.Explicit.MachineSubdivisionInit.atStage`, `OAI.MaxCutGames.Explicit.MachineSubdivisionLoopFrame.afterGuard`, `OAI.MaxCutGames.Explicit.MachineSubdivisionLoopFrame.bodyBits`, `OAI.MaxCutGames.Explicit.MachineSubdivisionLoopFrame.frame`, `OAI.MaxCutGames.Explicit.MachineSubdivisionLoopFrame.outputRows`, `OAI.MaxCutGames.Explicit.MachineSubdivisionLoopFrame.rowBits`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.guard`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.State`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.readRelationAt`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.readUnarySlots`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.readerStateEquiv`, `OAI.MaxCutGames.Foundations.Complexity.GraphCounterModel.machine`, `OAI.MaxCutGames.Foundations.Complexity.GraphCounterModel.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.fieldLoop`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.finishField`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.inputWord`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.rowEntry`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.rowTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.rowsTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.tableRows`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudCount.totalSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.inputLength`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.totalTime` and 138 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Estimates_Basic`, `MaxCut_Games_Basic`, `MaxCut_Games_RealTarget`, `MaxCut_Games_Subdivision`, `MaxCut_Games_TranslationTarget`, `MaxCut_Machines_Alphabet`, `MaxCut_Machines_CompareLoop`, `MaxCut_Machines_GraphCounterFinish`, `MaxCut_Machines_Input`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_Machine`, `MaxCut_Machines_MachineCloudCount`, `MaxCut_Machines_MachineCloudPadding`, `MaxCut_Machines_MachineCloudPrefix`, `MaxCut_Machines_MachineCloudSelect`, `MaxCut_Machines_MachineDummyRows`, `MaxCut_Machines_MachineExpanderTableProgram`, `MaxCut_Machines_MachineFieldProfile`, `MaxCut_Machines_MachineInitialHeaders`, `MaxCut_Machines_MachineLazyRows`, `MaxCut_Machines_MachineLazyTableRuntime`, `MaxCut_Machines_MachineLookupCore`, `MaxCut_Machines_MachineOverlayTable`, `MaxCut_Machines_MachinePaddedOverlay`, `MaxCut_Machines_MachineRegisterEmit`, `MaxCut_Machines_MachineRegularLift`, `MaxCut_Machines_MachineRegularMetadata`, `MaxCut_Machines_MachineRegularOriginalBody`, `MaxCut_Machines_MachineRegularOwnerProgram`, `MaxCut_Machines_MachineRegularTableRuntime`, `MaxCut_Machines_MachineRegularVertexBlock`, `MaxCut_Machines_MachineStateFrame`, `MaxCut_Machines_MachineSubdivisionDynamicRows`, `MaxCut_Machines_MachineSubdivisionEmission`, `MaxCut_Machines_MachineSubdivisionTableRead`, `MaxCut_Machines_MachineSubroutine`, `MaxCut_Machines_RawInitialMachineCleanup`, `MaxCut_Machines_Runtime2`, `MaxCut_Machines_RuntimeSpace`, `MaxCut_Machines_SelectorMachine`, `MaxCut_PCP_ExpanderFamily`, `MaxCut_PCP_Generator`, `MaxCut_PCP_GraphGap`, `MaxCut_PCP_KernelIteration`, `MaxCut_PCP_Overlap`, `MaxCut_PCP_PortTables`, `MaxCut_PCP_PreprocessingInternalRows`, `MaxCut_PCP_PreprocessingLazyWords`, `MaxCut_PCP_PreprocessingOverlayWords`, `MaxCut_PCP_PreprocessingPaddingOffsets`, `MaxCut_PCP_PreprocessingPaddingWords`, `MaxCut_PCP_PreprocessingRegularTables`, `MaxCut_PCP_PreprocessingStageMaps`, `MaxCut_PCP_ProductCollisionBounds`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_Rounding`, `MaxCut_PCP_SpectralCut`.
--
--   **Imports.** It imports the bundles `OAIQ087A007`, `OAIQ087A008`, `OAIQ087A009` and `OAIQ087A010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A022`, `OAIQ087A023`, `OAIQ087A024`, `OAIQ087A025`, `OAIQ087A026` and `OAIQ087A027`; the proof of `OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A007
import Definitions.Def_OAIQ087A008
import Definitions.Def_OAIQ087A009
import Definitions.Def_OAIQ087A010

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RealTarget
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arbitrary-real-error target and its exact passage from encoded rational
gap reductions. The same formula map and actual machine certificate are reused;
choosing smaller error tolerances does not change the computation. -/

/-!
The value of the actual finite Unique Games instance is its maximum satisfied
constraint fraction. Maximization ranges over every finite vertex labeling;
the denominator counts stored constraint occurrences, including repetitions.
The natural-number maximum totalizes an empty labeling type at zero. The
attainment and threshold equivalences require a positive alphabet.
-/

namespace MaxCutGames.Integration.InstanceValue

open MaxCutGames.Foundations
open Target

theorem maxSatisfied_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      countSatisfied labeling g.constraints = maxSatisfied g := by
  have inhabited : (Finset.univ : Finset (Fin g.vertices → Fin q)).Nonempty :=
    ⟨fun _ => ⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨labeling, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ inhabited
    (fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
  exact ⟨labeling, hmax.symm⟩

theorem value_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length = value g := by
  obtain ⟨labeling, hlabeling⟩ := maxSatisfied_attained g hq
  exact ⟨labeling, by rw [hlabeling]; rfl⟩

/-- Existential real completeness is precisely a lower bound on instance value. -/
theorem exists_rate_ge_iff {q : Nat} (g : Instance q) (hq : 0 < q) (a : ℝ) :
    (∃ labeling : Fin g.vertices → Fin q,
      a ≤ (countSatisfied labeling g.constraints : ℝ) / g.constraints.length) ↔
      a ≤ value g := by
  constructor
  · rintro ⟨labeling, hlabeling⟩
    exact hlabeling.trans (labeling_rate_le_value g labeling)
  · intro hvalue
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact ⟨labeling, hlabeling.symm ▸ hvalue⟩

/-- Universal real soundness is precisely an upper bound on instance value. -/
theorem forall_rate_le_iff {q : Nat} (g : Instance q) (hq : 0 < q) (b : ℝ) :
    (∀ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ b) ↔
      value g ≤ b := by
  constructor
  · intro hall
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact hlabeling ▸ hall labeling
  · intro hvalue labeling
    exact (labeling_rate_le_value g labeling).trans hvalue

end MaxCutGames.Integration.InstanceValue

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_TranslationTarget
attribute [-instance] _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.UniformTarget

open MaxCutGames.Foundations Target Complexity
open MaxCutGames.Integration
open MachineUniformCopyOrder

theorem count_append_inline_UniformTarget {n q : Nat} (a : Fin n → Fin q)
    (xs ys : List (Constraint n q)) :
    countSatisfied a (xs ++ ys) = countSatisfied a xs + countSatisfied a ys := by
  simp [GapSemantics.countSatisfied_eq_sum]

theorem count_copies {n q : Nat} (C : Nat) (es : List (Constraint n q))
    (a : Fin n → Fin q) :
    countSatisfied a (copyMajor C es) = C * countSatisfied a es := by
  induction C with
  | zero => simp [copyMajor, countSatisfied]
  | succ C ih =>
    change countSatisfied a (es ++ copyMajor C es) = _
    rw [count_append_inline_UniformTarget, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (a : Fin g.vertices → Fin q) :
    countSatisfied a (construct C hC g).constraints = C * countSatisfied a g.constraints :=
  count_copies C g.constraints a

theorem maxSatisfied {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.maxSatisfied (construct C hC g) = C * InstanceValue.maxSatisfied g := by
  classical
  apply Nat.le_antisymm
  · unfold InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro a _
    change countSatisfied a (copyMajor C g.constraints) ≤ C * InstanceValue.maxSatisfied g
    erw [count_copies]
    exact Nat.mul_le_mul_left C (InstanceValue.countSatisfied_le_maxSatisfied g a)
  · obtain ⟨a, ha⟩ := InstanceValue.maxSatisfied_attained g hq
    rw [← ha, ← count C hC g a]
    exact InstanceValue.countSatisfied_le_maxSatisfied (construct C hC g) a

theorem value {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.value (construct C hC g) = InstanceValue.value g := by
  have hc : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hm : (g.constraints.length : ℝ) ≠ 0 := by
    exact_mod_cast g.constraintCount_positive.ne'
  unfold InstanceValue.value
  rw [maxSatisfied C hC g hq, edge_count]
  push_cast
  field_simp

theorem mem_original {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (c : Constraint g.vertices q) (hc : c ∈ (construct C hC g).constraints) :
    c ∈ g.constraints := by
  obtain ⟨es, hes, hc⟩ := List.mem_flatten.mp hc
  have he : es = g.constraints := List.eq_of_mem_replicate hes
  simpa [he] using hc

theorem flatMap_copies {α β : Type*} (C : Nat) (xs : List α) (f : α → List β) :
    (copyMajor C xs).flatMap f = copyMajor C (xs.flatMap f) := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      List.flatMap_append] using congrArg (fun ys => xs.flatMap f ++ ys) ih

/-- The complete output keeps the two first headers and scales the edge count. -/
theorem gameWords_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameWords (construct C hC g) =
      [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (g.constraints.flatMap constraintWords) := by
  simp only [gameWords, vertices]
  rw [show (construct C hC g).constraints = copyMajor C g.constraints from rfl,
    flatMap_copies, copy_length]

theorem gameBits_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameBits (construct C hC g) =
      encodeWords [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (encodeWords (g.constraints.flatMap constraintWords)) := by
  rw [gameBits, gameWords_construct, encodeWords_append, encode_copies]

end MaxCutGames.Explicit.UniformTarget

end OAI
end

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

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

end MaxCutGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
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

namespace MaxCutGames.Foundations.Complexity.MachineRepeat
open Turing

def program (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Label M → TM2.Stmt (Symbols M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr .bodyToTemp)) M.m (auxProgram M input output)

def machine (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := Tape M
  kFin := by letI := M.kFin; exact inferInstanceAs (Fintype (Tape M))
  k₀ := .inl M.k₀
  k₁ := .inr .output
  Γ := Symbols M
  Λ := Label M
  ΛFin := by letI := M.ΛFin; exact inferInstanceAs (Fintype (Label M))
  main := .inr .parse
  σ := State M
  σFin := by
    letI := M.σFin
    letI := M.Γk₀Fin
    exact inferInstanceAs (Fintype (State M))
  initialState := (M.initialState,none)
  Γk₀Fin := M.Γk₀Fin
  m := program M input output

def embedded (M : FinTM2) (counter : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .bodyToTemp)) (none : Option (M.Γ M.k₀))
    (extraTapes M counter [] []) c

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_true (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm true :: word) counter) =
    some (inputConfig M .parse word (input.symm true :: counter)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm true :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input_inline_MachineRepeat, inputTapes_update_counter_inline_MachineRepeat,
    inputConfig]

theorem parseStep_false (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm false :: word) counter) =
    some (inputConfig M .guard word counter) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm false :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input_inline_MachineRepeat, inputTapes_update_counter_inline_MachineRepeat,
    inputConfig]

theorem parseTrace (count : Nat) (word counter : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[count+1]
      (some (inputConfig M .parse ((encodeWord count).map input.symm ++ word) counter)) =
    some (inputConfig M .guard word (List.replicate count (input.symm true) ++ counter)) := by
  induction count generalizing counter with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, List.map_singleton,
      List.singleton_append, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some]
      using! parseStep_false M input output word counter
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[count+1]
      ((machine M input output).step
        (inputConfig M .parse ((encodeWord (count+1)).map input.symm ++ word) counter)) = _
    simp only [encodeWord, List.replicate_succ, List.cons_append, List.map_cons,
      List.map_append, List.map_replicate]
    rw [parseStep_true]
    have h := ih (input.symm true :: counter)
    have hc : List.replicate count (input.symm true) ++ input.symm true :: counter =
        input.symm true :: (List.replicate count (input.symm true) ++ counter) := by
      rw [← List.singleton_append, ← List.append_assoc,
        ← List.replicate_succ', List.replicate_succ, List.cons_append]
    rw [hc] at h
    simpa only [encodeWord, List.map_append, List.map_replicate, List.map_singleton,
      List.map_nil, List.singleton_append, List.append_assoc] using! h

theorem guardStep_some (word counter : List (M.Γ M.k₀)) (symbol : M.Γ M.k₀) :
    (machine M input output).step (inputConfig M .guard word (symbol :: counter)) =
      some (embedded M counter (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word (symbol :: counter))) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter_inline_MachineRepeat,
    embedded, MachineEmbedding.configuration]
  exact ⟨rfl,rfl,rfl⟩

theorem guardStep_none (word : List (M.Γ M.k₀)) :
    (machine M input output).step (inputConfig M .guard word []) =
      some (inputConfig M .finalToTemp word []) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word [])) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter_inline_MachineRepeat,
    inputConfig]

/-- Lift the actual certified body run while preserving the remaining counter. -/
def bodyExecution (counter : List (M.Γ M.k₀))
    (word : List (M.Γ M.k₀)) (result : List (M.Γ M.k₁)) (budget : Nat)
    (run : TM2OutputsInTime M word (some result) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (initList M word))
      (some (embedded M counter (haltList M result))) budget :=
  MachineComposition.embeddedExecution (some (.inr .bodyToTemp : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M counter [] []) M.m
    (auxProgram M input output) run

theorem bodyToTemp_tapes_inline_MachineRepeat (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (.inl M.k₁) (.inr .temporary)
      (embedded M counter (haltList M result)).stk []
      (result.reverse.map (fun b => input.symm (output b))) =
    temporaryTapes M (result.reverse.map (fun b => input.symm (output b))) counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
        MachineEmbedding.configuration, haltList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
      MachineEmbedding.configuration, extraTapes]

theorem tempToOutput_tapes_inline_MachineRepeat (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inr .output)
      (temporaryTapes M word []) [] word.reverse =
        (haltList (machine M input output) word.reverse).stk := by
  funext k
  cases k with
  | inl k => simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList, machine]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList,
      machine, extraTapes]; rfl

theorem inputConfig_init_inline_MachineRepeat (word : List (M.Γ M.k₀)) :
    inputConfig M .parse word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes,initList,machine]; rfl
    · simp [inputTapes,initList,machine,h]
  | inr k => cases k <;> simp [inputTapes,initList,machine,extraTapes]

end MaxCutGames.Foundations.Complexity.MachineRepeat

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

namespace MaxCutGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-- Counter, temporary, and output tapes of the actual repeat machine all use
the body's finite input alphabet; body tapes retain their original alphabets. -/
theorem repeat_machine (body : FinTM2)
    (input : body.Γ body.k₀ ≃ Bool) (output : body.Γ body.k₁ ≃ Bool)
    (hbody : FiniteAlphabet body) :
    FiniteAlphabet (MachineRepeat.machine body input output) := by
  intro tape
  cases tape with
  | inl tape => exact hbody tape
  | inr _ => exact input_finite body

end MaxCutGames.Foundations.Complexity.MachineFiniteAlphabet

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

namespace MaxCutGames.Explicit.MachineUniformRun

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MachineUniformProgram

theorem repeated_template (C : Nat) (fields : Fin 4 → List Bool) :
    MachineFieldTemplate.templateOutput (List.replicate C (.copy 3)) fields =
      MachineUniformCopyOrder.copyMajor C (fields 3) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simp only [List.replicate_succ, MachineFieldTemplate.templateOutput,
      List.flatMap_cons, MachineFieldTemplate.tokenOutput,
      MachineUniformCopyOrder.copyMajor, List.flatten_cons] at *
    rw [ih]

theorem template_output (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) = outputBits C n q Q body := by
  simp only [tokens, MachineFieldTemplate.templateOutput, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, MachineFieldTemplate.tokenOutput]
  rw [show (List.replicate C (MachineFieldTemplate.Token.copy (3 : Fin 4))).flatMap
      (MachineFieldTemplate.tokenOutput (fun i => afterScale C n q Q body (emitField i))) =
        MachineUniformCopyOrder.copyMajor C (afterScale C n q Q body (emitField 3)) from
      repeated_template C _]
  simp [afterScale, MachineUniformHeaders.resultTapes, emitField, outputBits,
    encodeWords, List.append_assoc]

theorem template_copiedLength (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) =
        n + q + C * Q + 3 + C * body.length := by
  simp [MachineFieldTemplate.copiedLength, tokens, afterScale,
    MachineUniformHeaders.resultTapes, emitField, Nat.add_assoc] ; omega

end MaxCutGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionDynamicRows
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

namespace MaxCutGames.Explicit.MachineSubdivisionDynamicRows

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionRows (identityTable inverseTable)

/-- The last table is the actual table for the left-to-right `v → r` row. -/
def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, p⟩]

def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)

end MaxCutGames.Explicit.MachineSubdivisionDynamicRows

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

/-! Exact execution of the three input-header reads of subdivision. -/

namespace MaxCutGames.Explicit.MachineSubdivisionHeaders

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineSubdivisionProgram

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabetHeader
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabetHeader) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

end MaxCutGames.Explicit.MachineSubdivisionHeaders

/-! Physical header arithmetic and private-vertex initialization. -/

namespace MaxCutGames.Explicit.MachineSubdivisionInit

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

theorem frame_destination (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).destination =
      priorWord (initOp i).seed (beforeValue n i) := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes,
    afterValue, sourceValue, beforeValue, priorWord]

def atStage (q r : Nat) : Label q :=
  if h : r < 9 then .initialize_ ⟨r, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

theorem initNext_eq_atStage (q : Nat) (i : Fin 9) :
    (initNext i : Label q) = atStage q (i.val + 1) := by
  simp [initNext, atStage]

theorem final_frame (n q Q : Nat) (body : List Bool) :
    frame n q Q body 9 = resultTapes n q Q body := by
  funext tape
  cases tape <;>
    simp [frame, resultTapes, initOp, MachineSubdivisionHeaders.resultTapes,
      afterValue, sourceValue, beforeValue, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]

end MaxCutGames.Explicit.MachineSubdivisionInit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLookupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem fieldTapes_eq (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output input' output' : List Bool) :
    Hastad.SourceMachine.fieldTapes source destination
      (tapes index source destination base counter input output) input' output' =
      tapes index source destination base counter input' output' := by
  rw [Hastad.SourceMachine.fieldTapes, update_source _ _ _ hsd, update_destination]

end MaxCutGames.Foundations.Complexity.MachineLookup

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- The same exact trace packaged for composition with ambient machine phases. -/
def discardInTime (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := discardTrace source loopLabel returnLabel program atLoop
    base n suffix hinput ambient register
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineLookup

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace MaxCutGames.Foundations.Games

open scoped BigOperators

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem value_le_one (G : Game Q₁ Q₂ A₁ A₂) : G.value ≤ 1 :=
  (G.value_le_iff 1).2 G.success_le_one

end Game

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

end MaxCutGames.Foundations.Games

/-!
Exact finite sampling laws used to identify verifier distributions with repeated
game question laws. These are finite sum/product identities, not independence
assumptions about an unspecified distribution.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Overlap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Direct diagonal-overlap comparison for the finite correlated sampler.
All quantities are finite weight arrays; no reference sampler or embedding
claim is assumed. The final theorem consumes the per-label lower bound that
is proved for the actual finite threshold sampler in CorrelatedSampling.
-/

/-!
Correlated rounding of finite partial assignments of equal density. A common
finite list of seeds is scanned locally at every vertex. An edge succeeds when
the first seed accepted by either endpoint is a jointly accepted good seed.
The finite truncation error is at most `(1 - density)^n`. Maximizing over the finite
set of deterministic labelings removes that error. No infinite random seed or
assumed rounding principle is used.
-/

namespace MaxCutGames.Repetition

section

open MaxCutGames.Foundations.Games
open MaxCutGames.Foundations.CorrelatedSampling
open MaxCutGames.Foundations.Repetition
open scoped BigOperators

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

omit [Fintype V] [Fintype A] in
theorem partial_mass_bounds_inline_RoundingSampling (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (density : ℝ)
    (hdensity : ∀ v, μ.probability (accept v) = density) (x y : V) :
    0 ≤ partialPairMass μ accept label R x y ∧
    partialPairMass μ accept label R x y ≤ density ∧
    density ≤ μ.probability (fun s => accept x s || accept y s) ∧
    μ.probability (fun s => accept x s || accept y s) +
      partialPairMass μ accept label R x y ≤ 2 * density := by
  refine ⟨μ.probability_nonnegative _, ?_, ?_, ?_⟩
  · rw [← hdensity x]
    apply μ.probability_mono
    intro s hs
    have hp : (accept x s = true ∧ accept y s = true) ∧
        R x y (label x s) (label y s) = true := by simpa using hs
    exact hp.1.1
  · rw [← hdensity x]
    exact μ.probability_mono (fun s hs => by simp [hs])
  · calc
      _ ≤ μ.probability (accept x) + μ.probability (accept y) := by
        unfold partialPairMass FiniteDistribution.probability
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro s _
        cases hx : accept x s <;> cases hy : accept y s <;>
          cases hr : R x y (label x s) (label y s) <;>
          simp [hx, hy, hr] ; linarith [μ.nonnegative s]
      _ = 2 * density := by rw [hdensity x, hdensity y]; ring

omit [Fintype V] [Fintype A] in
/-- Pointwise success bound for the actual shared finite first-accept sampler.
The relation may depend on the ordered pair and need not be symmetric. -/
theorem partialSample_pair_lower (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (fallback : A) (density : ℝ)
    (hdensity₀ : 0 < density) (hdensity : ∀ v, μ.probability (accept v) = density)
    (x y : V) (n : Nat) :
    2 * (partialPairMass μ accept label R x y / density) - 1 - (1 - density) ^ n ≤
      traceAverage μ.weight n (fun proposals =>
        if R x y (partialSample accept label fallback proposals x)
          (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  let union : S → Bool := fun s => accept x s || accept y s
  let good : S → Bool := fun s =>
    accept x s && accept y s && R x y (label x s) (label y s)
  obtain ⟨hg, hgl, hlu, hug⟩ := partial_mass_bounds_inline_RoundingSampling μ accept label R density hdensity x y
  have hu : 0 < eventMass μ.weight union := lt_of_lt_of_le hdensity₀ hlu
  have hm : eventMass μ.weight (fun s => union s && good s) =
      partialPairMass μ accept label R x y := by
    unfold eventMass partialPairMass FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro s _
    cases hx : accept x s <;> cases hy : accept y s <;> simp [union, good, hx, hy]
  have hfirst := goodFirstMass_lower_bound μ.weight union good
    μ.nonnegative μ.normalized hu n
  rw [hm] at hfirst
  have hactual := traceAverage_mono μ.weight μ.nonnegative n _ _
    (first_good_relation_le_inline_RoundingSampling accept label R fallback x y)
  rw [goodFirstIndicator_law μ.weight _ _ μ.normalized n] at hactual
  have hcompl := eventMass_complement μ.weight union μ.normalized
  have hre : eventMass μ.weight (fun s => !(union s)) ≤ 1 - density := by
    change density ≤ eventMass μ.weight union at hlu
    linarith
  have hp := pow_le_pow_left₀
    (eventMass_nonneg μ.weight (fun s => !(union s)) μ.nonnegative) hre n
  have hr := partial_ratio_bound_inline_RoundingSampling hdensity₀ hg hgl hlu hug
  change 2 * (partialPairMass μ accept label R x y / density) - 1 ≤
    partialPairMass μ accept label R x y / eventMass μ.weight union at hr
  change goodFirstMass μ.weight union good n ≤ _ at hactual
  linarith

/-- Finite partial-assignment correlated rounding. Every vertex has acceptance
probability `density`. The normalized accepted good-pair mass `T` gives an actual
deterministic labeling with success at least `2*T - 1`. -/
theorem exists_labeling_ge_partial {E : Type*} [Fintype E] [Nonempty V] [Nonempty A]
    (μ : FiniteDistribution S) (ν : FiniteDistribution E)
    (accept : V → S → Bool) (label : V → S → A)
    (left right : E → V) (R : E → A → A → Bool) (density : ℝ) (hdensity₀ : 0 < density)
    (hdensity : ∀ v, μ.probability (accept v) = density) :
    ∃ f : V → A,
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 ≤
        partialLabelScore ν left right R f := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨best, _, hbest⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (V → A))) Finset.univ_nonempty (partialLabelScore ν left right R)
  have hmax (f : V → A) :
      partialLabelScore ν left right R f ≤ partialLabelScore ν left right R best := by
    rw [← hbest]
    exact Finset.le_sup' (partialLabelScore ν left right R) (Finset.mem_univ f)
  have hbounded (n : Nat) :
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 -
        (1 - density) ^ n ≤ partialLabelScore ν left right R best := by
    let seeds := traceSeedLaw μ n
    let sample := fun seed => partialSample accept label fallback (traceList n seed)
    have hpoint (e : E) := partialSample_pair_lower μ accept label (fun _ _ => R e)
      fallback density hdensity₀ hdensity (left e) (right e) n
    change ∀ e : E, 2 * (partialEdgeMass μ accept label left right R e / density) - 1 -
      (1 - density) ^ n ≤ traceAverage μ.weight n (fun proposals =>
        if R e (partialSample accept label fallback proposals (left e))
          (partialSample accept label fallback proposals (right e)) then 1 else 0) at hpoint
    have hlower := expectation_mono_inline_RoundingSampling' ν hpoint
    rw [expectation_partial_lower_inline_RoundingSampling] at hlower
    have hswitch :
        ν.expectation (fun e => traceAverage μ.weight n (fun proposals =>
          if R e (partialSample accept label fallback proposals (left e))
            (partialSample accept label fallback proposals (right e)) then 1 else 0)) =
        seeds.expectation (fun seed => partialLabelScore ν left right R (sample seed)) := by
      simp_rw [← traceSeedLaw_expectation μ n]
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro seed
      simp [partialLabelScore, FiniteDistribution.probability,
        FiniteDistribution.expectation, sample, mul_ite]
    rw [hswitch] at hlower
    have hupper := expectation_mono_inline_RoundingSampling' seeds (fun seed => hmax (sample seed))
    rw [expectation_const_inline_RoundingSampling'] at hupper
    exact hlower.trans hupper
  refine ⟨best, ?_⟩
  have hdensity₁ : density ≤ 1 := by
    rw [← hdensity (Classical.choice (inferInstance : Nonempty V))]
    exact μ.probability_le_one _
  by_contra hn
  have hgap : 0 <
      (2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1) -
        partialLabelScore ν left right R best := sub_pos.mpr (lt_of_not_ge hn)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - density)
    (by linarith : 1 - density < 1)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hgap)).exists
  linarith [hbounded n]

end

/-!
Exact finite threshold expansion for unit vectors.  A shared seed chooses one
coordinate and one atom of the common threshold partition.  Squared amplitudes
are acceptance probabilities, and joint acceptance has the coordinatewise
minimum law.  The construction permits arbitrary vertex-dependent labels and
arbitrary relations between their labels.
-/

open scoped BigOperators
open Foundations Games CorrelatedSampling

end MaxCutGames.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Rounding
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! High-value rounding of finite nonnegative vectors. The finite threshold
partition and bounded shared rejection sampler produce an ordinary deterministic
labeling. The auxiliary edge sample may retain hidden constraint information;
the labeling receives only its local vertex. -/

namespace MaxCutGames.Repetition

section

open scoped BigOperators
open Foundations.Games

variable {V E A Ω : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype Ω]
  [Nonempty V] [Nonempty A] [Nonempty Ω]

/-- Unit squared row mass converts a large collision energy into a genuinely
local deterministic labeling. All randomness used by the proof is independent
of the sampled constraint, and the final answer has no random seed. -/
theorem exists_labeling_high_value (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_ge_partial
    (thresholdDistribution f) ν (thresholdAccept f) (thresholdLabel f a)
    left right R (thresholdRate Ω) thresholdRate_positive
    (threshold_acceptance_mass f hrow)
  rw [threshold_average_good_mass ν left right R a f hrow,
    mul_div_cancel_left₀ _ (ne_of_gt (thresholdRate_positive (Ω := Ω)))] at hlabels
  have hoverlap := pairOverlap_ge_energy ν left right R a f hf hrow
  refine ⟨labels, ?_⟩
  linarith

omit [Nonempty Ω] in
/-- Rows of mass at most one are completed by private vertex coordinates.
Their nonnegative contribution only improves the collision energy. -/
theorem exists_labeling_high_value_of_rows_le_one (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value ν left right R
    (paddedLabel a fallback) (paddedAmplitude f)
    (paddedAmplitude_nonnegative f hf) (paddedAmplitude_row f hrow)
  have henergy := pairEnergy_le_padded ν left right R a f hf fallback
  have hsqrt := Real.sqrt_le_sqrt (show
      2 * (1 - pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f)) ≤
        2 * (1 - pairEnergy ν left right R a f) by linarith)
  exact ⟨labels, (by linarith :
    1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      1 - 2 * Real.sqrt
        (2 * (1 - pairEnergy ν left right R (paddedLabel a fallback)
          (paddedAmplitude f)))).trans hlabels⟩

omit [Nonempty Ω] in
/-- A genuine gap for every deterministic labeling bounds the vector energy
by an alphabet-independent quadratic gap. -/
theorem pairEnergy_le_of_labeling_gap (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ labels : V → A, partialLabelScore ν left right R labels ≤ 1 - g) :
    pairEnergy ν left right R a f ≤ 1 - g ^ 2 / 8 := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value_of_rows_le_one
    ν left right R a f hf hrow
  have hbound := hlabels.trans (hgap labels)
  have he : pairEnergy ν left right R a f ≤ 1 := by
    by_contra h
    have hneg : 2 * (1 - pairEnergy ν left right R a f) ≤ 0 := by linarith
    rw [Real.sqrt_eq_zero_of_nonpos hneg] at hbound
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (1 - pairEnergy ν left right R a f) by linarith)
  have hgs : g ≤ 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) := by
    linarith
  have hsq := mul_self_le_mul_self hg.le hgs
  nlinarith

end

/-!
Determinization of a nonnegative vector with one label chosen per vertex.
Every vertex retains its total mass. The objective is an arbitrary nonnegative
weighted sum of squares of linear functionals, so coefficients may have either
sign. Sampling complete label tables gives the original vector as its mean;
finite variance and an attained maximum then supply a deterministic table.
-/

/-!
Finite conditional projection kernels for the Dinur--Steurer argument.
The outer distribution samples the right question and the inner distribution
samples the left question conditional on it. These are genuine normalized
finite distributions; no norm inequality or repetition claim is a field.
-/

open MaxCutGames.Foundations.Games
open scoped BigOperators

end MaxCutGames.Repetition

/-!
The collision norm as an actual finite distribution on symmetrized edges.
An edge retains the hidden common right question, while each label remains a
function of its own left question.  Projection uniqueness turns the sum over
common right answers into a Boolean compatibility predicate exactly.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ProductCollisionBounds
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the actual classical game value with the squared collision
norm. Both directions are proved for the normalized conditional kernel, including
partial projection constraints and zero-weight questions. -/

namespace MaxCutGames.Repetition

noncomputable section

namespace ProjectionKernel

open MaxCutGames.Foundations.Games
open scoped BigOperators

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem apply_assignment_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) (b : A₂) :
    0 ≤ K.apply (assignment labels) y b := by
  rw [apply_assignment]
  exact (K.inner y).probability_nonnegative (fun x => K.accepts x y (labels x) b)

theorem value_sq_le_collisionValue [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.toGame.value ^ 2 ≤ K.collisionValue := by
  obtain ⟨s, hs⟩ := K.toGame.exists_optimal_strategy
  rw [← hs]
  exact (K.success_sq_le_assignmentEnergy s).trans (K.assignmentEnergy_le_collisionValue s.1)

theorem assignmentEnergy_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    K.assignmentEnergy labels ≤ K.toGame.value := by
  obtain ⟨answers, hanswers⟩ := K.exists_best_response labels
  calc
    _ ≤ K.toGame.success (labels, answers) := by
      rw [success_eq_outer_apply]
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      calc
        _ ≤ ∑ b, K.apply (assignment labels) y b *
            K.apply (assignment labels) y (answers y) := by
          apply Finset.sum_le_sum
          intro b _
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (hanswers y b)
            (K.apply_assignment_nonneg labels y b)
        _ = (∑ b, K.apply (assignment labels) y b) *
            K.apply (assignment labels) y (answers y) := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * K.apply (assignment labels) y (answers y) :=
          mul_le_mul_of_nonneg_right (K.sum_apply_assignment_le_one labels y)
            (K.apply_assignment_nonneg labels y (answers y))
        _ = _ := one_mul _
    _ ≤ K.toGame.value := K.toGame.success_le_value _

theorem collisionValue_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.collisionValue ≤ K.toGame.value :=
  (K.collisionValue_le_iff _).mpr K.assignmentEnergy_le_value

theorem collisionValue_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : K.collisionValue ≤ 1 :=
  K.collisionValue_le_value.trans K.toGame.value_le_one

/-! The alphabet-independent high-value bound for the actual projection
operator. Positive vectors are determinized, padded, and rounded using proved
finite constructions. No rounding or repetition hypothesis is exposed. -/

/-- Unit mass form of the Dinur--Steurer positive-vector approximation bound.
The loss is independent of both alphabets and of the auxiliary dimension. -/
theorem vectorEnergy_le_gap_rate [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ 1)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - g) :
    K.vectorEnergy f ≤ 1 - g ^ 2 / 8 := by
  classical
  let : Nonempty Q₂ := distribution_nonempty_inline_RoundingKernel K.outer
  let : Nonempty Q₁ := distribution_nonempty_inline_RoundingKernel
    (K.inner (Classical.choice (inferInstance : Nonempty Q₂)))
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · let : IsEmpty Ω := hΩ
    have hzero : K.vectorEnergy f = 0 := by simp [vectorEnergy]
    rw [hzero]
    have hsq : g * g ≤ (1 : ℝ) * 1 := mul_le_mul hg1 hg1 hg0 (by norm_num)
    nlinarith
  · let : Nonempty Ω := hΩ
    obtain ⟨labels, hdet⟩ := K.exists_vectorEnergy_le_singleLabelVector f hf
    have hnonneg := vectorAmplitude_nonnegative f hf
    have hrow : ∀ x, rowSquareMass (vectorAmplitude f) x ≤ 1 := by
      intro x
      rw [rowSquareMass_vectorAmplitude]
      exact hmass x
    rw [K.vectorEnergy_singleLabelVector] at hdet
    by_cases hg : g = 0
    · subst g
      simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
      let fallback : A₁ := Classical.choice inferInstance
      have hpad := pairEnergy_le_padded K.symmetricDistribution symmetricLeft
        symmetricRight K.symmetricAccept labels (vectorAmplitude f) hnonneg fallback
      have hone := pairEnergy_le_one_of_unit_rows K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept
        (paddedLabel labels fallback) (paddedAmplitude (vectorAmplitude f))
        (paddedAmplitude_row (vectorAmplitude f) hrow)
      exact hdet.trans (hpad.trans hone)
    · have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hg)
      have hscore (a : Q₁ → A₁) :
          partialLabelScore K.symmetricDistribution symmetricLeft symmetricRight
            K.symmetricAccept a ≤ 1 - g := by
        unfold partialLabelScore
        rw [K.symmetric_probability_eq_assignmentEnergy]
        exact (K.assignmentEnergy_le_collisionValue a).trans
          (K.collisionValue_le_value.trans hvalue)
      exact hdet.trans (pairEnergy_le_of_labeling_gap K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept labels (vectorAmplitude f)
        hnonneg hrow hgpos hscore)

end ProjectionKernel

/-!
Finite-sum tensor factorization used by projection-game collision operators.
No restriction to coordinatewise strategies occurs: `f` below is an arbitrary
function of both input questions and both input answers.
-/

end

end MaxCutGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_KernelIteration
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Independent repetitions of the actual conditional projection kernel. The
resulting game has precisely the original game's product question law. A
successor tuple is a reindexed independent product, so collision bounds on the
product apply to unrestricted strategies on whole tuples.
-/

namespace MaxCutGames.Repetition.ProjectionKernel

open MaxCutGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem collisionValue_repetition_zero_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    (K.repetition 0).collisionValue ≤ 1 :=
  (K.repetition 0).collisionValue_le_one

end
end MaxCutGames.Repetition.ProjectionKernel

/-!
The finite product algebra of dependency breaking.

Revealing one endpoint of each independently sampled question pair turns the
remaining question weight into a product of two separate functions, one for
each player. Further separate restrictions on the players' answers preserve
this product. The final theorem normalizes the displayed weights, rather than
assuming conditional independence as an abstract hypothesis.
-/

/-! Normalized local completion laws derived from their actual product weights.
Zero rows use explicit default laws and satisfy the same recombination identity.
-/

/-!
Every finite projection game has an exact conditional-kernel representation.
The right question uses its original marginal. Conditional left-question laws
are normalized original rows; zero rows use the original left marginal as a
fallback. Their zero outer weight makes the reconstruction identity valid on
all rows without positivity or support hypotheses.
-/

/-!
Alphabet-independent repetition of ordinary finite projection games.

The game is the actual finite question distribution and its local acceptance
predicate. The proof bounds nonnegative vector assignments by finite
thresholding and correlated sampling, factors each unrestricted product
strategy through that bound, and iterates the resulting collision contraction.
No repetition bound, decoder certificate, or alphabet-size budget is a premise.

The deterministic-predicate game interface permits arbitrary real question
weights. Distinct hidden constraints on the same question pair are not encoded
by this interface. Both v2 uses have a unique predicate for each question pair:
the distinct-position equation--variable game and the final simple graph.
-/

namespace MaxCutGames.Repetition
open MaxCutGames.Foundations.Games
noncomputable section

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
  [Nonempty A₁] [Nonempty A₂] [Nonempty B₁] [Nonempty B₂]

omit [Nonempty B₂] in
theorem collisionValue_product_le_gap_rate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) :
    (K.product H).collisionValue ≤ (1 - gap ^ 2 / 8) * H.collisionValue := by
  apply ((K.product H).collisionValue_le_iff _).2
  intro labels
  rw [← vectorEnergy_tensorSlice]
  apply K.vectorEnergy_le_of_unit_bound (1 - gap ^ 2 / 8) H.collisionValue
    (fun f hf hmass => K.vectorEnergy_le_gap_rate f hf hmass hgap₀ hgap₁ hvalue)
    H.collisionValue_nonneg (H.tensorSlice labels)
    (H.tensorSlice_nonnegative labels) (H.vectorMass_tensorSlice_le labels)

theorem repetition_value_le_dsRate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) (n : ℕ) :
    (K.toGame.repetition n).value ≤ dsRate gap ^ n := by
  have hstep : ∀ m, (K.repetition (m + 1)).collisionValue ≤
      (1 - gap ^ 2 / 8) * (K.repetition m).collisionValue := by
    intro m
    rw [K.collisionValue_repetition_succ]
    exact K.collisionValue_product_le_gap_rate (K.repetition m) hgap₀ hgap₁ hvalue
  have h := rate_of_squared_collision_recurrence hgap₀ hgap₁
    (fun m => (K.repetition m).collisionValue)
    (fun m => (K.repetition m).toGame.value)
    K.collisionValue_repetition_zero_le_one hstep
    (fun m => (K.repetition m).value_sq_le_collisionValue) n
  simpa only [toGame_repetition] using h

end ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

/-- The v2 projection-repetition estimate, including the empty product.
The repetition exponent is independent of all question and answer cardinalities. -/
theorem projection_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    {gap : ℝ} (hgap₀ : 0 < gap) (hgap₁ : gap < 1)
    (hvalue : G.value ≤ 1 - gap) :
    (G.repetition n).value ≤ (1 - gap ^ 2 / 16) ^ n := by
  have h := (kernelOfGame G hG).repetition_value_le_dsRate hgap₀.le hgap₁.le
    (by simpa only [kernelOfGame_value] using hvalue) n
  simpa only [toGame_kernelOfGame, dsRate] using h

theorem final_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 10240000) ^ n := by
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 800) (by norm_num) (by norm_num) hvalue
  norm_num at h ⊢
  exact h

end
end MaxCutGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubroutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace MaxCutGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem steps_le_table (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value)
    (ha : a ≤ (encodeWords values).length) :
    steps values a coefficient offset ≤ 7 * (encodeWords values).length + 6 := by
  have h := steps_le values a coefficient offset value selected
  omega

end MaxCutGames.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineStateFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit ambient a) =
      some (configuration labels exit ambient b) := by
  have framed : TM2.step (frameProgram source) (frameConfiguration ambient a) =
      some (frameConfiguration ambient b) := by
    rw [frame_step, h]
    rfl
  exact MachineSubroutine.step_simulation labels exit (frameProgram source) target
    atLabels _ _ framed

def execution (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit ambient a) (some (configuration labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels) run

@[simp] theorem execution_steps (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    (execution labels exit ambient source target atLabels run).steps = run.steps := rfl

end MaxCutGames.Foundations.Complexity.MachineStateFrame

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFieldProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

namespace MaxCutGames.Foundations.Complexity.MachineFieldProfile

open Turing

def storePair {q : Nat} (pair : Fin q × Fin q) (bit : Bool)
    {Λ : Type} (nextLabel : Λ) :
    TM2.Stmt (fun _ : Tape q => Bool) Λ (MachineCompare.State (Profile q)) :=
  .load (fun state => normalState (setEntry state.1 pair bit)) (.goto fun _ => nextLabel)

/-- The fixed list of pairs determines all control labels and original fields.
The program compares only copied work-stack heads, then stores one finite bit. -/
def profileProgram {q : Nat} (cells : List (Fin q × Fin q)) (label : Label cells) :
    TM2.Stmt (fun _ : Tape q => Bool) (Label cells) (MachineCompare.State (Profile q)) :=
  if h : label.1.val < cells.length then
    let pair := cells[label.1.val]
    let r := label.1.val
    match label.2.val with
    | 0 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.1) (.inr 2) id false
        (labelAt cells r 0) (some (labelAt cells r 1)))
    | 1 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.1) (.inr 0) false
        (labelAt cells r 1) (some (labelAt cells r 2)))
    | 2 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.2) (.inr 2) id false
        (labelAt cells r 2) (some (labelAt cells r 3)))
    | 3 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.2) (.inr 1) false
        (labelAt cells r 3) (some (labelAt cells r 4)))
    | 4 => MachineCompare.loop (.inr 0) (.inr 1) (labelAt cells r 4)
        (some (labelAt cells r 5)) (some (labelAt cells r 6))
    | 5 => storePair pair true (labelAt cells (r + 1) 0)
    | _ => storePair pair false (labelAt cells (r + 1) 0)
  else .halt

/-- A concrete finite machine for the full field equality matrix. -/
def profileMachine (q : Nat) : FinTM2 where
  K := Tape q
  k₀ := .inr 0
  k₁ := .inr 0
  Γ _ := Bool
  Λ := Label (allPairs q)
  main := labelAt (allPairs q) 0 0
  σ := MachineCompare.State (Profile q)
  initialState := normalState (fun _ _ => false)
  m := profileProgram (allPairs q)

end MaxCutGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegisterEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegisterEmit

open Turing
open MaxCutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

/-- Caller-program form of the full exact trace. No execution premise is used. -/
theorem registerEmitTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 5]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩ := by
  have copied := MachineCopy.copyTrace source destination scratch sourceDestination
    sourceScratch destinationScratch false firstLabel secondLabel (some emitLabel)
    program atFirst atSecond base scratchEmpty ambient register
  rw [sourceWord, encodeWord_length] at copied
  rw [show 2 * n + 5 = 1 + 2 * (n + 1 + 1) by omega,
    Function.iterate_add_apply, copied, Function.iterate_one]
  change TM2.step program
    ⟨some emitLabel, (ambient, none),
      Function.update base destination (encodeWord n ++ base destination)⟩ = _
  rw [emitStep destination offset emitLabel exit program atEmit]
  simp only [Function.update_self, Function.update_idem]
  rw [← List.append_assoc, prefix_encodeWord]

end MaxCutGames.Foundations.Complexity.MachineRegisterEmit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

namespace MaxCutGames.Foundations.PCP.GraphTables

open MaxCutGames.Foundations.Complexity

/-- A concrete encoding suitable for the existing TM2 computation interface. -/
def encoding : Computability.Encoding Table Bool where
  encode := tableBits
  decode := decodeTableBits
  decode_encode := decodeTableBits_encoded

/-- At least one unary delimiter is stored for every field, including all
4096 entries of every predicate table. -/
theorem tableWords_length_le_bits (table : Table) :
    2 + 4098 * table.darts ≤ (tableBits table).length := by
  rw [tableBits, encodeWords_length, ← tableWords_length]
  omega

theorem relationBits_length_le (relation : RelationTable) :
    (encodeWords (relationWords relation)).length ≤ 8192 := by
  have h := encodeWords_length_le (relationWords relation) 1 (by
    intro word hword
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hword
    cases bit <;> decide)
  simpa only [relationWords_length] using h

theorem rowBits_length_le {n m : Nat} (row : DartRow n m) :
    (encodeWords (rowWords row)).length ≤ n + m + 8192 := by
  have ht := row.tail.isLt
  have hr := row.reverseIndex.isLt
  have hp := relationBits_length_le row.relation
  simp only [rowWords, encodeWords_append, List.length_append, encodeWords,
    encodeWord_length, List.length_nil] at ⊢
  omega

theorem rowsBits_length_le {n m : Nat} (rows : List (DartRow n m)) :
    (encodeWords (rows.flatMap rowWords)).length ≤ rows.length * (n + m + 8192) := by
  induction rows with
  | nil => simp [encodeWords]
  | cons row rows ih =>
      have hrow := rowBits_length_le row
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Full unary size bound: headers, both bounded indices in every row, and
every Boolean predicate entry are counted. This is not a runtime assertion. -/
theorem tableBits_length_le (table : Table) :
    (tableBits table).length ≤ table.vertices + table.darts + 2 +
      table.darts * (table.vertices + table.darts + 8192) := by
  have hrows := rowsBits_length_le (rowList table)
  rw [rowList_length] at hrows
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem vertices_le_tableBits_length (table : Table) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem darts_le_tableBits_length (table : Table) :
    table.darts ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end MaxCutGames.Foundations.PCP.GraphTables

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PortTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable regular constraint tables on the fixed 64-label alphabet

Every pair `(vertex,port)` has one stored reverse index and one complete
4096-bit relation. Flat row `port + ports * vertex` has its tail implicitly
fixed by that pair. Rotation uses the stored vector lookup, followed by the
inverse row-index bijection. Loops and repeated directed occurrences remain
distinct rows.

Serialization uses the existing `GraphTables` codec: header `[vertices,darts]`
with `darts=vertices*ports`, then tail/reverse/4096 bit words per row.
-/

namespace MaxCutGames.Foundations.PCP.PortTables

open PoweringWalks

variable {n d : Nat}

def graphTable (table : Table n d) : GraphTables.Table :=
  ⟨n, n * d, flatRows table, flatRows_valid table⟩

/-- Existing graph codec, with header `[n,n*d]` and 4098 words in every row. -/
def tableWords (table : Table n d) : List Nat := GraphTables.tableWords (graphTable table)

def tableBits (table : Table n d) : List Bool := GraphTables.tableBits (graphTable table)

def inputBits {ports : Nat} (input : Input ports) : List Bool := tableBits input.2

theorem tableWords_eq (table : Table n d) :
    tableWords table = [n, n * d] ++ (flatRows table).toList.flatMap GraphTables.rowWords := rfl

theorem vertices_le_tableBits_length (table : Table n d) : n ≤ (tableBits table).length :=
  GraphTables.vertices_le_tableBits_length (graphTable table)

end MaxCutGames.Foundations.PCP.PortTables

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

/-- Filtering preserves the original ordering, including repeated row values
at different dart indices. -/
theorem cloudDarts_sublist (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Sublist (List.finRange t.darts) := List.filter_sublist

theorem cloudSize_le_darts (t : Table) (v : Fin t.vertices) :
    cloudSize t v ≤ t.darts := by
  simpa only [cloudSize, List.length_finRange] using (cloudDarts_sublist t v).length_le

theorem cloudSize_eq_card_cloud (t : Table) (v : Fin t.vertices) :
    cloudSize t v = Fintype.card (Cloud (semantics t) v) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (cloudEquiv t v)).symm

theorem sum_cloudSize (t : Table) : (∑ v, cloudSize t v) = t.darts := by
  calc
    _ = ∑ v, Fintype.card (Cloud (semantics t) v) := by
      apply Finset.sum_congr rfl
      intro v _
      exact cloudSize_eq_card_cloud t v
    _ = Fintype.card (Fin t.darts) := CloudPadding.sum_card_cloud (semantics t)
    _ = t.darts := Fintype.card_fin t.darts

end MaxCutGames.Foundations.PCP.PreprocessingCloudIndex

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

variable {Λ σ : Type}

def finishField (restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .load (fun state => ((state.1.1, false), none)) (.goto fun _ => restore)

def fieldLoop (again restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .target (fun state _ => (state.1, none))
            (.push .scratch (fun _ => true) (.goto fun _ => again)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => again))))
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => !state.1.2 && !(state.2.getD false))
          (.push .count (fun _ => true) (finishField restore))
          (finishField restore))))

theorem fieldStep_zero (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord 0 ++ suffix) (encodeWord v ++ targetSuffix)
          scratch count spare⟩ =
      some ⟨some restore, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) scratch
          (List.replicate (hit flag 0 v) true ++ count) spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  cases v <;> cases flag <;>
    simp [fieldLoop, finishField, TM2.stepAux, encodeWord, hit, List.replicate_succ]

theorem fieldStep_succ_zero (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord (x + 1) ++ suffix) (encodeWord 0 ++ targetSuffix)
          scratch count spare⟩ =
      some ⟨some again, ((ambient, true), none),
        memory original (encodeWord x ++ suffix) (encodeWord 0 ++ targetSuffix)
          scratch count spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  simp [fieldLoop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem fieldStep_succ_succ (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord (x + 1) ++ suffix)
          (encodeWord (v + 1) ++ targetSuffix) scratch count spare⟩ =
      some ⟨some again, ((ambient, flag), none),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          (true :: scratch) count spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  simp [fieldLoop, TM2.stepAux, encodeWord, List.replicate_succ]

/-- The actual field-reading trace. The scratch holds exactly the consumed
target bits, and the output increment records equality of the complete field. -/
theorem fieldTrace (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[x + 1]
      (some ⟨some again, ((ambient, flag), register),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          scratch count spare⟩) =
      some ⟨some restore, ((ambient, false), none),
        memory original suffix (encodeWord (v - x) ++ targetSuffix)
          (List.replicate (min x v) true ++ scratch)
          (List.replicate (hit flag x v) true ++ count) spare⟩ := by
  induction x generalizing v scratch flag register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some, Nat.sub_zero,
        Nat.zero_min, List.replicate_zero, List.nil_append] using
        fieldStep_zero again restore program atField original suffix targetSuffix spare v
          scratch count ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[x + 1]
        (TM2.step program ⟨some again, ((ambient, flag), register),
          memory original (encodeWord (x + 1) ++ suffix) (encodeWord v ++ targetSuffix)
            scratch count spare⟩) = _
      cases v with
      | zero =>
          rw [fieldStep_succ_zero again restore program atField]
          simpa [hit] using ih 0 scratch true none
      | succ v =>
          rw [fieldStep_succ_succ again restore program atField]
          simpa [hit, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih v (true :: scratch) flag none

theorem replicate_encodeWord (a b : Nat) :
    List.replicate a true ++ encodeWord b = encodeWord (a + b) := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]

/-- The actual restoring transfer returns every consumed target bit. -/
theorem preservingFieldTrace (again restore next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (atRestore : program restore = Reduction.MachineTransfer.loopAt
      .scratch .target id false restore (some next))
    (original suffix targetSuffix count spare : List Bool) (x v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[x + min x v + 2]
      (some ⟨some again, ((ambient, false), register),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨some next, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true ++ count) spare⟩ := by
  have hfield := fieldTrace again restore program atField original suffix targetSuffix spare
    x v [] count ambient false register
  simp only [List.append_nil, hit, true_and] at hfield
  let after := memory original suffix (encodeWord (v - x) ++ targetSuffix)
    (List.replicate (min x v) true)
    (List.replicate (if x = v then 1 else 0) true ++ count) spare
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes
    Tape.scratch Tape.target (by decide) id false restore (some next) program atRestore
      after (ambient, false) none
  have hsum : min x v + (v - x) = v := by omega
  simp only [after, memory_scratch, memory_target, List.length_replicate,
    List.reverse_replicate, List.map_id, Reduction.MachineTransfer.tapesAt,
    update_memory_scratch, update_memory_target] at hrestore
  rw [← List.append_assoc, replicate_encodeWord, hsum] at hrestore
  rw [show x + min x v + 2 = (min x v + 1) + (x + 1) by omega,
    Function.iterate_add_apply, hfield]
  exact hrestore

/-- Consecutive concrete field-discard instructions consume a fixed list of
fields. The hypotheses specify code, not an abstract body execution. -/
theorem discardFieldsTrace (labels : Nat → Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (fields : List Nat) (offset : Nat)
    (atField : ∀ i, i < fields.length → program (labels (offset + i)) =
      MachineLookup.discard .work (labels (offset + i)) (labels (offset + i + 1)))
    (original suffix target scratch count spare : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords fields).length]
      (some ⟨some (labels offset), ((ambient, flag), register),
        memory original (encodeWords fields ++ suffix) target scratch count spare⟩) =
      some ⟨some (labels (offset + fields.length)),
        ((ambient, flag), if fields = [] then register else none),
        memory original suffix target scratch count spare⟩ := by
  induction fields generalizing offset register with
  | nil => simp only [encodeWords, List.length_nil, Function.iterate_zero_apply,
      List.nil_append, Nat.add_zero, ↓reduceIte]
  | cons x fields ih =>
      have hfirst := MachineLookup.discardTrace Tape.work (labels offset) (labels (offset + 1))
        program (by simpa only [Nat.add_zero] using atField 0 (by simp))
        (memory original (encodeWords (x :: fields) ++ suffix) target scratch count spare)
        x (encodeWords fields ++ suffix) (by simp only [memory_work, encodeWords, List.append_assoc])
        (ambient, flag) register
      simp only [update_memory_work] at hfirst
      have hrest := ih (offset + 1) (by
        intro i hi
        have h := atField (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h) none
      rw [show (encodeWords (x :: fields)).length =
          (encodeWords fields).length + (x + 1) by
          simp only [encodeWords, List.length_append, encodeWord_length]
          omega,
        Function.iterate_add_apply, hfirst]
      simpa only [List.length_cons, List.cons_ne_nil,
        ite_false, ite_self, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

def rowEntry : TM2.Stmt Alphabet Label (State σ) :=
  .peek .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .field))
      (.load (fun state => ((state.1.1, false), none)) .halt))

/-- A single fixed program copies the input once, skips two headers, then
compares the first field of each 4098-field row. -/
def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .original .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .original .work false .copySecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .row
  | .row => rowEntry
  | .field => fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .target id false .restore (some (skipLabel 0))
  | .skip i => MachineLookup.discard .work (.skip i) (skipLabel (i.val + 1))

theorem program_skip {i : Nat} (hi : i < 4097) :
    program (σ := σ) (skipLabel i) =
      MachineLookup.discard .work (skipLabel i) (skipLabel (i + 1)) := by
  simp only [skipLabel, dite_eq_left hi, program]

theorem rowStep_nonempty (original work target scratch count spare : List Bool)
    (hwork : work ≠ []) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .row, ((ambient, flag), register), memory original work target scratch count spare⟩ =
      some ⟨some .field, ((ambient, false), none),
        memory original work target scratch count spare⟩ := by
  cases work with
  | nil => exact (hwork rfl).elim
  | cons x xs => rfl

theorem rowStep_empty (original target scratch count spare : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .row, ((ambient, flag), register), memory original [] target scratch count spare⟩ =
      some ⟨none, ((ambient, false), none), memory original [] target scratch count spare⟩ := rfl

def rowTime (v : Nat) (r : Row) : Nat :=
  (encodeWords (rowWords r)).length + min r.1 v + 2

/-- One complete stored row is consumed; the target and original are restored. -/
theorem rowTrace (r : Row) (hwidth : r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix count spare : List Bool) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare⟩ := by
  have hfield := preservingFieldTrace Label.field Label.restore (skipLabel 0)
    program rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count spare r.1 v ambient none
  have hskip := discardFieldsTrace skipLabel (program (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using program_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (program (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step program ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count spare⟩) = _
  rw [rowStep_nonempty original _ _ [] count spare
    (by simp [rowWords, encodeWords, encodeWord]) ambient false register,
    Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

def rowsTime (v : Nat) : List Row → Nat
  | [] => 1
  | r :: rs => rowsTime v rs + rowTime v r

/-- The complete actual row scan halts with the number of matching tails. -/
theorem rowsTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original targetSuffix count spare : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowsTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords)) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨none, ((ambient, false), none),
        memory original [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) spare⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [rowsTime, List.flatMap_nil, encodeWords, Function.iterate_one, advance_some,
        rowsHits, List.replicate_zero, List.nil_append] using
        rowStep_empty original (encodeWord v ++ targetSuffix) [] count spare ambient false register
  | cons r rs ih =>
      have hrow := rowTrace r (hwidth r (by simp)) v original
        (encodeWords (rs.flatMap rowWords)) targetSuffix count spare ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [rowsTime, List.flatMap_cons, encodeWords_append]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem rowTime_le (v : Nat) (r : Row) :
    rowTime v r ≤ 3 * (encodeWords (rowWords r)).length := by
  have hmin := Nat.min_le_left r.1 v
  have hlen : r.1 + 1 ≤ (encodeWords (rowWords r)).length := by
    simp only [rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  unfold rowTime
  omega

theorem rowsTime_le (v : Nat) (rs : List Row) :
    rowsTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 1 := by
  induction rs with
  | nil => simp only [rowsTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [rowsTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

def inputWord (n m : Nat) (rs : List Row) : List Bool :=
  encodeWords ([n, m] ++ rs.flatMap rowWords)

theorem inputWord_eq (n m : Nat) (rs : List Row) :
    inputWord n m rs = encodeWord n ++ (encodeWord m ++ encodeWords (rs.flatMap rowWords)) := by
  simp only [inputWord, encodeWords_append, encodeWords, List.append_nil, List.append_assoc]

theorem inputWord_length (n m : Nat) (rs : List Row) :
    (inputWord n m rs).length = n + 1 + (m + 1) +
      (encodeWords (rs.flatMap rowWords)).length := by
  rw [inputWord_eq]
  simp only [List.length_append, encodeWord_length]
  omega

def totalSteps (n m v : Nat) (rs : List Row) : Nat :=
  2 * ((inputWord n m rs).length + 1) + (n + 1) + (m + 1) + rowsTime v rs

/-- One preserving copy, the two concrete header discards, and the proved row
scan form the complete execution. The input and target tapes are unchanged. -/
theorem countTrace (n m v : Nat) (rs : List Row)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (targetSuffix count : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps n m v rs]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) []⟩ := by
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.headerFirst) program rfl rfl
    (memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work Label.headerFirst Label.headerSecond
    program rfl
    (memory (inputWord n m rs) (inputWord n m rs) (encodeWord v ++ targetSuffix) [] count [])
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (by exact inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work Label.headerSecond Label.row
    program rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (encodeWord v ++ targetSuffix) [] count [])
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hrows := rowsTrace rs hwidth v (inputWord n m rs) targetSuffix count [] ambient none
  rw [show totalSteps n m v rs = rowsTime v rs + ((m + 1) + ((n + 1) +
      2 * ((inputWord n m rs).length + 1))) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (rowsTime v rs),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    hcopy, hfirst, hsecond]
  exact hrows

theorem totalSteps_le (n m v : Nat) (rs : List Row) :
    totalSteps n m v rs ≤ 5 * (inputWord n m rs).length + 3 := by
  have hrows := rowsTime_le v rs
  have hlen := inputWord_length n m rs
  unfold totalSteps
  omega

open MaxCutGames.Foundations.PCP

def tableRows (t : GraphTables.Table) : List Row :=
  (GraphTables.rowList t).map (fun r =>
    (r.tail.val, r.reverseIndex.val :: GraphTables.relationWords r.relation))

theorem tableRows_width (t : GraphTables.Table) :
    ∀ r ∈ tableRows t, r.2.length = 4097 := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  simp [GraphTables.relationWords]

theorem tableRows_words (t : GraphTables.Table) :
    (tableRows t).flatMap rowWords = (GraphTables.rowList t).flatMap GraphTables.rowWords := by
  simp only [tableRows, List.flatMap_map]
  apply congrArg (fun f => (GraphTables.rowList t).flatMap f)
  funext r
  rfl

theorem tableRows_input (t : GraphTables.Table) :
    inputWord t.vertices t.darts (tableRows t) = GraphTables.tableBits t := by
  rw [inputWord, tableRows_words]
  rfl

theorem rowList_eq_finRange_map (t : GraphTables.Table) :
    GraphTables.rowList t = (List.finRange t.darts).map (fun e => t.rows[e]) := by
  apply List.ext_getElem
  · simp [GraphTables.rowList]
  · intro i hi hj
    simp [GraphTables.rowList]

theorem rowList_cloud_count (t : GraphTables.Table) (v : Fin t.vertices) :
    ((GraphTables.rowList t).filter (fun r => decide (r.tail = v))).length =
      PreprocessingCloudIndex.cloudSize t v := by
  rw [rowList_eq_finRange_map, List.filter_map, List.length_map]
  rfl

theorem tableRows_hits (t : GraphTables.Table) (v : Fin t.vertices) :
    rowsHits v.val (tableRows t) = PreprocessingCloudIndex.cloudSize t v := by
  rw [rowsHits_eq_filter]
  simp only [tableRows, List.filter_map, List.length_map]
  simpa only [Function.comp_def, Fin.val_inj] using rowList_cloud_count t v

/-- Cloud size is produced by reading the actual encoded tail fields, with
the complete graph input and unary vertex query preserved on their tapes. -/
theorem cloudCountTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (targetSuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps t.vertices t.darts v.val (tableRows t)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudSize t v) ++ countSuffix) []⟩ := by
  have h := countTrace t.vertices t.darts v.val (tableRows t) (tableRows_width t)
    targetSuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, tableRows_hits, ← List.append_assoc, replicate_encodeWord, Nat.add_zero] at h
  exact h

end MaxCutGames.Foundations.Complexity.MachineCloudCount

namespace MaxCutGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

variable {σ : Type}

theorem replicate_encodeWord (a b : Nat) :
    List.replicate a true ++ encodeWord b = encodeWord (a + b) := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]

theorem timePolynomial_encoding (g k : Nat) :
    (timePolynomial g).eval (encodeWord k).length = timeBound g k := by
  simp [timePolynomial, timeBound, encodeWord_length]

end MaxCutGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cloud counting, geometric padding, and unary subtraction

One finite program places the checked cloud counter and geometric search on
shared tapes. Its final phase physically subtracts the preserved cloud size
from the computed power. A head test handles the empty cloud separately.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

/- Static placement of homogeneous tapes, with an explicit finite partial
inverse. Complement tapes are preserved by every simulated transition. -/

variable {σ : Type}

def totalTime (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  (1 + MachineCloudCount.totalSteps t.vertices t.darts v.val (MachineCloudCount.tableRows t)) +
    postTime (PreprocessingCloudIndex.cloudSize t v)

def inputLength (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) : Nat :=
  (GraphTables.tableBits t).length + (encodeWord v.val ++ suffix).length

theorem count_length_le (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) :
    PreprocessingCloudIndex.cloudSize t v + 1 ≤ inputLength t v suffix := by
  have h := (PreprocessingCloudIndex.cloudSize_le_darts t v).trans
    (GraphTables.darts_le_tableBits_length t)
  simp only [inputLength, List.length_append, encodeWord_length]
  omega

theorem table_length_le (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) :
    (GraphTables.tableBits t).length ≤ inputLength t v suffix := by
  unfold inputLength
  omega

theorem totalTime_le (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) :
    totalTime t v ≤ timePolynomial.eval (inputLength t v suffix) := by
  have hc := MachineCloudCount.totalSteps_le t.vertices t.darts v.val (MachineCloudCount.tableRows t)
  rw [MachineCloudCount.tableRows_input] at hc
  have hp := postTime_le (PreprocessingCloudIndex.cloudSize t v)
  have hk := count_length_le t v suffix
  have ht := table_length_le t v suffix
  have hsq := Nat.mul_le_mul_left (ExpanderFamily.growth + 8)
    (Nat.pow_le_pow_left hk 2)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  unfold MachineCeilingPower.timeBound at hp
  unfold totalTime
  omega

end MaxCutGames.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

/-- An empty cloud has a total, vacuous rotation table. -/
def emptyTable (q : Nat) : ExpanderTables.Table 0 q :=
  ExpanderTables.ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

/-- Change only a proof-equal size index, without selecting any new numbering. -/
def resizeTable {n m q : Nat} (h : n = m) (table : ExpanderTables.Table n q) :
    ExpanderTables.Table m q := h ▸ table

abbrev BaseTable := ExpanderTables.Table
  ((Expanders.baseDegree * Expanders.baseDegree) *
    (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree

end MaxCutGames.Foundations.PCP.PreprocessingRegularTables

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem reverseIndex_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (v.castLE h, p)] =
      rowIndex m d ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  rw [← rowIndex_rotation, rotation_pad_old]

theorem reverseIndex_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      rowIndex m d (vertexEquiv h (Sum.inr v), p) := by
  rw [← rowIndex_rotation, rotation_pad_new]

theorem relation_ext_inline_PreprocessingPaddingTables {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

/-- The entire old 4096-bit relation row is retained. -/
theorem relations_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).relations[rowIndex m d (v.castLE h, p)] =
      table.relations[rowIndex n d (v, p)] := by
  apply relation_ext_inline_PreprocessingPaddingTables
  intro a b
  exact accepts_pad_old table h v p a b

/-- Every bit of every added relation row PortTables.accepts. -/
theorem relations_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).relations[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      Vector.replicate 4096 true := by
  apply relation_ext_inline_PreprocessingPaddingTables
  intro a b
  simpa only [PortTables.accepts, GraphTables.relationAt, Fin.getElem_fin,
    Vector.getElem_replicate] using
    accepts_pad_new table h v p a b

end MaxCutGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingOffsets
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executable dummy numbering is the sum of earlier cloud sizes plus
the local dummy index. This connects the actual list search in vertexOrder
with unary prefix-sum routines, without changing the chosen enumeration. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

theorem paddingOrder_val {n : Nat} (padding : Fin n → Nat)
    (v : Fin n) (j : Fin (padding v)) :
    (PreprocessingRegularTables.paddingOrder padding ⟨v, j⟩).val =
      offset padding v.val + j.val := by
  change (paddingList padding).idxOf ⟨v, j⟩ = _
  have h := sigma_idxOf padding (List.finRange n) v (List.mem_finRange v) j
  simpa only [List.idxOf_finRange, paddingList, offset] using h

theorem vertexOrder_dummy_val (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (v : Fin t.vertices) (j : Fin (padding v)) :
    (vertexOrder t padding (Sum.inr ⟨v, j⟩)).val =
      t.darts + offset padding v.val + j.val := by
  rw [vertexOrder_dummy, paddingOrder_val]
  omega

end MaxCutGames.Foundations.PCP.PreprocessingPaddingOffsets

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open MaxCutGames.Foundations.PCP
open scoped BigOperators

@[simp] theorem update_frame_remaining (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .remaining x =
      frame a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_frame_total (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .total x =
      frame a b c d e f g x := by
  funext k; cases k <;> rfl

def paddingView : Tape → Option MachineCloudPadding.Tape
  | .inner k => some k
  | _ => none

theorem paddingView_left (k : MachineCloudPadding.Tape) : paddingView (.inner k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : paddingView j = some k) : Tape.inner k = j := by
  cases j <;> simp_all [paddingView]

theorem placedTapes (inner : MachineCloudPadding.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes paddingView inner extra =
      memory inner (extra .bound) (extra .remaining) (extra .total) := by
  funext j; cases j <;> rfl

variable {σ : Type}

def inputLength (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (GraphTables.tableBits t).length + (encodeWord b ++ suffix).length

end MaxCutGames.Foundations.Complexity.MachineCloudPrefix

namespace MaxCutGames.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- Exact copy, lookup, return, and residual-cleanup transition count. -/
def steps (values : List Nat) (index : Nat) : Nat :=
  (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) +
    ((encodeWords (values.drop (index + 1))).length + 1)

theorem remaining_length_le (values : List Nat) (index : Nat) :
    (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop (index + 1) values)
  simp only [encodeWords_append, List.length_append] at h
  omega

theorem steps_le (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ 6 * (encodeWords values).length + 4 := by
  have hc := MachinePreservingLookup.preservingLookup_steps_le values index value selected
  have hd := remaining_length_le values index
  unfold steps
  omega

/-- The framing representation is the caller's exact tape state whenever its
index and work tape contain the specified index and an empty list. -/
theorem initialTapes_eq (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) :
    MachinePreservingLookup.initialTapes tape base index indexSuffix [] (base (tape 3)) =
      base := by
  simp only [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
    ← counterWord, ← workEmpty, Function.update_eq_self]

end MaxCutGames.Foundations.Complexity.MachinePreservingLookupClean

namespace MaxCutGames.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

@[simp] theorem appendTapes_source (source destination : K)
    (distinct : source ≠ destination) (base : K → List β) :
    appendTapes source destination base source = [] := by
  simp [appendTapes, distinct]

@[simp] theorem appendTapes_destination (source destination : K) (base : K → List β) :
    appendTapes source destination base destination = base destination ++ base source := by
  simp [appendTapes]

theorem finalTapes_eq_inline_MachineAppendAt (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    Reduction.MachineTransfer.tapesAt scratch destination
      (secondTapes_inline_MachineAppendAt source destination scratch base) [] (base destination ++ base source) =
        appendTapes source destination base := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [appendTapes, secondTapes_inline_MachineAppendAt, firstTapes_inline_MachineAppendAt, Reduction.MachineTransfer.tapesAt,
      sourceDestination, sourceScratch]
  · by_cases hd : k = destination
    · subst k
      simp [appendTapes, Reduction.MachineTransfer.tapesAt]
    · by_cases ht : k = scratch
      · subst k
        simp [appendTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch,
          Ne.symm destinationScratch, scratchEmpty]
      · simp [appendTapes, secondTapes_inline_MachineAppendAt, firstTapes_inline_MachineAppendAt, Reduction.MachineTransfer.tapesAt,
          hs, hd, ht]

theorem appendTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel thirdLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt destination scratch
      id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = Reduction.MachineTransfer.loopAt source scratch
      id fallback secondLabel (some thirdLabel))
    (atThird : program thirdLabel = Reduction.MachineTransfer.loopAt scratch destination
      id fallback thirdLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[
        2 * ((base source).length + (base destination).length) + 3]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), appendTapes source destination base⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes destination scratch
    destinationScratch id fallback firstLabel (some secondLabel) program atFirst
    base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨some secondLabel, (ambient, none), firstTapes_inline_MachineAppendAt destination scratch base⟩ at first
  have firstSource : firstTapes_inline_MachineAppendAt destination scratch base source = base source := by
    simp [firstTapes_inline_MachineAppendAt, Reduction.MachineTransfer.tapesAt, sourceDestination, sourceScratch]
  have firstScratch : firstTapes_inline_MachineAppendAt destination scratch base scratch =
      (base destination).reverse := by
    simp [firstTapes_inline_MachineAppendAt]
  have second := Reduction.MachineTransfer.transferAt_fromTapes source scratch
    sourceScratch id fallback secondLabel (some thirdLabel) program atSecond
    (firstTapes_inline_MachineAppendAt destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (firstTapes_inline_MachineAppendAt destination scratch base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes_inline_MachineAppendAt destination scratch base⟩) = _
      at second
  rw [firstSource, firstScratch] at second
  simp only [List.map_id] at second
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes_inline_MachineAppendAt destination scratch base⟩) =
      some ⟨some thirdLabel, (ambient, none), secondTapes_inline_MachineAppendAt source destination scratch base⟩
        at second
  have secondScratch : secondTapes_inline_MachineAppendAt source destination scratch base scratch =
      (base source).reverse ++ (base destination).reverse := by
    simp [secondTapes_inline_MachineAppendAt]
  have secondDestination : secondTapes_inline_MachineAppendAt source destination scratch base destination = [] := by
    simp [secondTapes_inline_MachineAppendAt, firstTapes_inline_MachineAppendAt, Reduction.MachineTransfer.tapesAt,
      Ne.symm sourceDestination, destinationScratch]
  have third := Reduction.MachineTransfer.transferAt_fromTapes scratch destination
    (Ne.symm destinationScratch) id fallback thirdLabel exit program atThird
    (secondTapes_inline_MachineAppendAt source destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (secondTapes_inline_MachineAppendAt source destination scratch base scratch).length + 1]
    (some ⟨some thirdLabel, (ambient, none), secondTapes_inline_MachineAppendAt source destination scratch base⟩) = _
      at third
  rw [secondScratch, secondDestination] at third
  simp only [List.map_id, List.reverse_append, List.reverse_reverse, List.append_nil,
    List.length_append, List.length_reverse] at third
  rw [finalTapes_eq_inline_MachineAppendAt source destination scratch sourceDestination sourceScratch
    destinationScratch base scratchEmpty] at third
  rw [show 2 * ((base source).length + (base destination).length) + 3 =
      ((base source).length + (base destination).length + 1) +
        (((base source).length + 1) + ((base destination).length + 1)) by omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base source).length + 1)
    (n := (base destination).length + 1), first, second]
  exact third

end MaxCutGames.Foundations.Complexity.MachineAppendAt

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

theorem rotation_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (x : Fin n × Fin d) :
    PortTables.rotation (materialize G ports) x =
      ((G.reverse (x.1, ports.symm x.2)).1,
        ports (G.reverse (x.1, ports.symm x.2)).2) := by
  simp only [materialize, PortTables.rotation_ofPortGraph, GraphTransport.reindex,
    Overlay.originalPortGraph, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm, Equiv.refl_apply, Prod.map]
  rfl

theorem rotation_materialize_image {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (v : Fin n) (i : D) :
    PortTables.rotation (materialize G ports) (v, ports i) =
      ((G.reverse (v, i)).1, ports (G.reverse (v, i)).2) := by
  rw [rotation_materialize, Equiv.symm_apply_apply]

end MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SpectralCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/

/-!
An actual fixed-degree graph obtained by padding each outgoing-dart cloud to
the explicit expander family and then replacing vertices by cloud darts.
Expansion and majority rounding are proved dependencies, not hypotheses of
the final soundness theorem. Isolated original vertices have empty clouds.
-/

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

abbrev BaseTable := PreprocessingRegularTables.BaseTable

end MaxCutGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Input
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Input

open MaxCutGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph bitWord relationWords relationWords_length rowWords rowWords_length
  )

variable {q n m : Nat}

/-- Exact decomposition before, at, and after a selected stored row. -/
theorem rowsWords_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    rows.flatMap rowWords = (rows.take e).flatMap rowWords ++
      (rowWords rows[e] ++ (rows.drop (e + 1)).flatMap rowWords) := by
  have hs : rows.take e ++ rows[e] :: rows.drop (e + 1) = rows := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow q n m) => rs.flatMap rowWords) hs
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hw.symm

/-- The unary serialization keeps exactly the same row boundaries, with
separate encoded prefixes rather than an assumed constant bit offset. -/
theorem rowsBits_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    encodeWords (rows.flatMap rowWords) =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          encodeWords ((rows.drop (e + 1)).flatMap rowWords)) := by
  rw [rowsWords_split rows e he]
  simp only [encodeWords_append]

/-- A selected row can be followed by an arbitrary caller-owned suffix. -/
theorem rowsBits_append_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) (suffix : List Bool) :
    encodeWords (rows.flatMap rowWords) ++ suffix =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          (encodeWords ((rows.drop (e + 1)).flatMap rowWords) ++ suffix)) := by
  rw [rowsBits_split rows e he]
  simp only [List.append_assoc]

end MaxCutGames.Foundations.PCP.AlphabetTable.Input

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Lookup
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

theorem stepAux_skipBits (source : K) (bits : List Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (skipBits source bits.length next) (ambient, register)
        (Function.update base source (encodeWords (bits.map bitWord) ++ suffix)) =
      TM2.stepAux next (ambient, none) (Function.update base source suffix) := by
  induction bits generalizing register with
  | nil => simp [skipBits, encodeWords, TM2.stepAux]
  | cons bit bits ih =>
    cases bit <;>
      simpa only [List.length_cons, skipBits, List.map_cons, bitWord, Bool.false_eq_true,
        ite_false, ite_true, if_true, encodeWords, encodeWord, List.replicate_zero,
        List.replicate_succ, List.nil_append, List.cons_append, List.singleton_append,
        TM2.stepAux, Function.update_self, List.head?_cons, List.tail_cons,
        Option.getD_some, Bool.cond_false, Bool.cond_true, Function.update_idem] using
          ih none

end MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CompareLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open MaxCutGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

theorem output_encodeWord_inline_Emitter (coefficient n : Nat) :
    Reduction.MachineTransducer.output transition (payload coefficient) () (encodeWord n) =
      List.replicate (coefficient * n) true := by
  induction n with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ n ih =>
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, ite_true, if_true, transition]
    change List.replicate coefficient true ++
      Reduction.MachineTransducer.output transition (payload coefficient) () (encodeWord n) = _
    rw [ih, ← List.replicate_add]
    congr 1
    simp [Nat.mul_succ, Nat.add_comm]

def prefixBits {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) (ambient : σ) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixBits commands values ambient r ++
      commandBits values ambient (commandAt commands r)

def prefixSteps {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => prefixSteps commands values r + commandSteps values (commandAt commands r)

theorem prefixSteps_le {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) (N : Nat) (bounded : ∀ i, values i ≤ N)
    (r : Nat) : prefixSteps commands values r ≤ r * (3 * (N + 1) + 3) := by
  induction r with
  | zero => simp [prefixSteps]
  | succ r ih =>
    have one : commandSteps values (commandAt commands r) ≤ 3 * (N + 1) + 3 := by
      cases commandAt commands r with
      | literal _ => simp only [commandSteps]; omega
      | bit _ => simp only [commandSteps]; omega
      | bounded _ => simp only [commandSteps]; omega
      | scaled source _ => have hs := bounded source; simp only [commandSteps]; omega
      | scaledIf source _ _ => have hs := bounded source; simp only [commandSteps]; omega
    calc
      prefixSteps commands values (r + 1) =
          prefixSteps commands values r + commandSteps values (commandAt commands r) := rfl
      _ ≤ r * (3 * (N + 1) + 3) + (3 * (N + 1) + 3) := Nat.add_le_add ih one
      _ = (r + 1) * (3 * (N + 1) + 3) := (Nat.succ_mul r _).symm

theorem prefixBits_listCommands (commands : List (Command h σ bound))
    (values : Fin h → Nat) (ambient : σ) (r : Nat) (hr : r ≤ commands.length) :
    prefixBits (listCommands commands) values ambient r =
      (commands.take r).flatMap (commandBits values ambient) := by
  induction r with
  | zero => simp [prefixBits]
  | succ r ih =>
    have hrc : r < commands.length := by omega
    rw [prefixBits, ih (by omega), List.take_succ_eq_append_getElem hrc,
      List.flatMap_append]
    simp [commandAt, hrc, listCommands]

theorem bits_listCommands (commands : List (Command h σ bound))
    (values : Fin h → Nat) (ambient : σ) :
    prefixBits (listCommands commands) values ambient commands.length =
      commands.flatMap (commandBits values ambient) := by
  simpa using prefixBits_listCommands commands values ambient commands.length (Nat.le_refl _)

theorem scaleBits_inline_Emitter (terms : List (Fin h × Nat)) (values : Fin h → Nat) (ambient : σ) :
    (terms.map (fun term => (Command.scaled term.1 term.2 : Command h σ bound))).flatMap
      (commandBits values ambient) =
    List.replicate ((terms.map (fun term => term.2 * values term.1)).sum) true := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    simp only [List.map_cons, List.flatMap_cons, commandBits, List.sum_cons]
    rw [ih, List.replicate_add]

theorem affineCommands_bits (terms : List (Fin h × Nat)) (offset : σ → Fin bound)
    (values : Fin h → Nat) (ambient : σ) :
    (affineCommands terms offset).flatMap (commandBits values ambient) =
      encodeWord (affineValue terms values (offset ambient).val) := by
  simp only [affineCommands, List.flatMap_append, scaleBits_inline_Emitter, List.flatMap_cons,
    List.flatMap_nil, commandBits, List.append_nil, affineValue, encodeWord,
    List.replicate_add, List.append_assoc]

end MaxCutGames.Foundations.PCP.AlphabetTable.Emitter

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

def bitEncoding (bit : Bool) : List Bool := encodeWord (if bit then 1 else 0)

end MaxCutGames.Foundations.Complexity.MachineUnaryEqualityBit

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open MaxCutGames.Foundations.PCP

/-! ## Fixed finite relation calculation -/

abbrev Field (S : Nat) := (GraphTables.Label × GraphTables.Label) ⊕ (Fin S ⊕ Fin S)

def fieldEquiv (S : Nat) : Field S ≃ Fin (4096 + (S + S)) :=
  (Equiv.sumCongr GraphTables.relationIndex
    (finSumFinEquiv : (Fin S ⊕ Fin S) ≃ Fin (S + S))).trans finSumFinEquiv

def inputEquiv (t S : Nat) : (Fin t × Field S) ≃ Fin (inputSize t S) :=
  (Equiv.prodCongr (Equiv.refl (Fin t)) (fieldEquiv S)).trans finProdFinEquiv

/-- Proof-level organization of exactly the finite bits physically read. -/
def packData {t S : Nat} (data : Fin t → Field S → Bool) : Buffer (inputSize t S) :=
  fun i => data ((inputEquiv t S).symm i).1 ((inputEquiv t S).symm i).2

@[simp] theorem packData_inputEquiv {t S : Nat}
    (data : Fin t → Field S → Bool) (k : Fin t) (f : Field S) :
    packData data (inputEquiv t S (k, f)) = data k f := by
  simp [packData]

def basePredicate {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (a b : GraphTables.Label) : Bool :=
  bits (inputEquiv t S (k, .inl (a, b)))

def leftMatches {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (i : Fin S) : Bool :=
  bits (inputEquiv t S (k, .inr (.inl i)))

def rightMatches {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (i : Fin S) : Bool :=
  bits (inputEquiv t S (k, .inr (.inr i)))

/-- `labelAt` is a fixed finite lookup table determined by the reduction
parameters, for example `decodeLabel a (allAddresses.get i)`. -/
def edgeAccept {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) : Bool :=
  match firstMatch (leftMatches bits k), firstMatch (rightMatches bits k) with
  | some i, some j => basePredicate bits k (labelAt a i) (labelAt b j)
  | _, _ => false

def rowAccept {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) : Bool :=
  (List.ofFn id).all (fun k : Fin t => edgeAccept labelAt bits k a b)

/-- Every powered-label pair is written in the canonical row-major order. -/
def rowBlock {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) : Buffer (q * q) :=
  fun i => rowAccept labelAt bits
    ((GenericGraphTables.relationIndex q).symm i).1
    ((GenericGraphTables.relationIndex q).symm i).2

@[simp] theorem rowBlock_at {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowBlock labelAt bits (GenericGraphTables.relationIndex q (a, b)) =
      rowAccept labelAt bits a b := by
  simp [rowBlock]

/-! ## Actual unary Boolean field instructions -/

@[simp] theorem encodeBits_append (xs ys : List Bool) :
    encodeBits (xs ++ ys) = encodeBits xs ++ encodeBits ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [encodeBits, ih, List.append_assoc]

section Chains

variable {K Λ σ : Type} {N : Nat}

/-- Read one zero-delimited unary Boolean field for each fixed register slot.
The second pop occurs exactly when the value is one. -/
def readEncodedSlots (src : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop src (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop src (fun state _ => state) (readEncodedSlots src slots next))
          (readEncodedSlots src slots next))

variable [DecidableEq K]

theorem stepAux_readEncodedSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readEncodedSlots src slots next) (ambient, buffer)
        (Function.update tapes src (encodeBits (slots.map bits) ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readEncodedSlots, encodeBits, fill]
  | cons i slots ih =>
      cases hb : bits i <;>
        simpa only [readEncodedSlots, List.map_cons, encodeBits, encodeBit, hb,
          Bool.false_eq_true, ite_false, ite_true, if_true, List.cons_append,
          List.nil_append, TM2.stepAux, Function.update_self, List.head?_cons,
          Option.getD_some, List.tail_cons, Function.update_idem, Bool.cond_false,
          Bool.cond_true, fill, List.foldl_cons] using
          ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readEncodedAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (readEncodedSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readEncodedSlots src (List.ofFn id) next
    state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src
      (encodeBits ((List.ofFn id).map bits) ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

/-- The delimiter is pushed first, then the optional unary one; writing slots
in reverse order gives the canonical field order on the destination stack. -/
def writeEncodedSlots {M : Nat} (dst : K) (emit : σ → Buffer M) : List (Fin M) →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | i :: slots, next => .push dst (fun _ => false)
      (.branch (fun state => emit state i)
        (.push dst (fun _ => true) (writeEncodedSlots dst emit slots next))
        (writeEncodedSlots dst emit slots next))

theorem stepAux_writeEncodedSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeEncodedSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst
          (encodeBits ((slots.map (emit state)).reverse) ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeEncodedSlots, encodeBits]
  | cons i slots ih =>
      cases hb : emit state i <;>
        simp only [writeEncodedSlots, TM2.stepAux, hb, Bool.cond_false, Bool.cond_true]
      all_goals rw [ih]
      all_goals simp [Function.update_idem, List.map_cons, List.reverse_cons,
        encodeBits_append, encodeBits, encodeBit, hb, List.append_assoc]

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readEncodedSlots src (List.ofFn id)
    (writeEncodedSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  encodedBlockStmt src dst F (finishAt exit)

variable [DecidableEq K]

theorem stepAux_encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst)) := by
  unfold encodedBlockStmt
  rw [stepAux_readEncodedAll src _ state bits tapes suffix hinput,
    stepAux_writeEncodedSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, stepAux_encodedBlockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

end Block

/-! ## Concrete row machine and its actual one-step execution -/

end MaxCutGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition

/-! The outer construction uses independent finite registers for its existing
subprograms. This transport combines tape placement, an untouched register
frame, and a static register equivalence, without adding any machine steps. -/
namespace Lift

open MachineCloudPadding

variable {K K' Λ Λ' σ τ υ : Type}

variable [DecidableEq K] [DecidableEq K']

theorem stepAux (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit registers q) (registers (state, ambient))
        (Placement.tapes view source extra) =
      configuration view labels exit registers ambient extra (TM2.stepAux q state source) := by
  rw [statement, MachineStateEquiv.stepAux_transport, MachineStateFrame.frame_stepAux,
    Placement.stepAux_simulation tape view left right]
  rfl

theorem step (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit registers ambient extra a) =
      some (configuration view labels exit registers ambient extra b) := by
  cases a with
  | mk label state sourceTapes =>
    cases label with
    | none => simp [TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (source label) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels label)) (registers (state, ambient))
        (Placement.tapes view sourceTapes extra)) = _
      rw [code, stepAux tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (steps : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (run : (advance (TM2.step source))^[steps] (some a) = some b) :
    (advance (TM2.step target))^[steps]
      (some (configuration view labels exit registers ambient extra a)) =
      some (configuration view labels exit registers ambient extra b) :=
  liftSuccessfulTrace _ _ _
    (step tape view left right labels exit registers ambient extra source target code) steps a b run

end Lift

end MaxCutGames.Foundations.Complexity.MachineRegularTable

namespace MaxCutGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

/-- Specification of the trace length; this function is not part of control. -/
def prefixTime (v : Nat) : List Row → Nat
  | [] => 2
  | r :: rs => prefixTime v rs + rowTime v r

def queryWord (v k : Nat) (suffix : List Bool) : List Bool :=
  encodeWord v ++ (encodeWord k ++ suffix)

def rankSteps (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) : Nat :=
  2 * ((queryWord v k querySuffix).length + 1) + (v + 1) +
    2 * ((inputWord n m rs).length + 1) + (n + 1) + (m + 1) +
      prefixTime v (rs.take k)

open MaxCutGames.Foundations.PCP

end MaxCutGames.Foundations.Complexity.MachineCloudRank

namespace MaxCutGames.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

/-- `fields 0`, `fields 1`, and `fields 2` are the tail, reverse index, and
encoded relation tapes. Every instruction reads or writes a single tape head. -/
def routine (fields : Fin 3 → K) (row output scratch : K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .relationRead => Reduction.MachineTransfer.loopAt (fields 2) scratch id false
      (labels .relationRead) (some (labels .relationRestore))
  | .relationRestore => MachineCopy.forkLoop scratch (fields 2) row false
      (labels .relationRestore) (some (labels .reverseRead))
  | .reverseRead => Reduction.MachineTransfer.loopAt (fields 1) scratch id false
      (labels .reverseRead) (some (labels .reverseRestore))
  | .reverseRestore => MachineCopy.forkLoop scratch (fields 1) row false
      (labels .reverseRestore) (some (labels .tailRead))
  | .tailRead => Reduction.MachineTransfer.loopAt (fields 0) scratch id false
      (labels .tailRead) (some (labels .tailRestore))
  | .tailRestore => MachineCopy.forkLoop scratch (fields 0) row false
      (labels .tailRestore) (some (labels .appendOld))
  | .appendOld => Reduction.MachineTransfer.loopAt output scratch id false
      (labels .appendOld) (some (labels .appendRow))
  | .appendRow => Reduction.MachineTransfer.loopAt row scratch id false
      (labels .appendRow) (some (labels .appendBack))
  | .appendBack => Reduction.MachineTransfer.loopAt scratch output id false
      (labels .appendBack) exit

/-- The three actual preserving-copy phases, with exact tape handoffs. -/
theorem prefixTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowScratch : row ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (fieldSize fields base + 3)]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨some (labels .appendOld), (ambient, none), prefixTapes fields row base⟩ := by
  let afterRelation := Function.update base row (base (fields 2) ++ base row)
  let afterReverse := Function.update afterRelation row
    (base (fields 1) ++ afterRelation row)
  have hfirst := MachineCopy.copyTrace (fields 2) row scratch
    (hfields 2).1 (hfields 2).2 hrowScratch false
    (labels .relationRead) (labels .relationRestore) (some (labels .reverseRead))
    program (hprogram .relationRead) (hprogram .relationRestore) base hscratch ambient register
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 2)).length + 1)]
    (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
    some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩ at hfirst
  have hsecond := MachineCopy.copyTrace (fields 1) row scratch
    (hfields 1).1 (hfields 1).2 hrowScratch false
    (labels .reverseRead) (labels .reverseRestore) (some (labels .tailRead))
    program (hprogram .reverseRead) (hprogram .reverseRestore) afterRelation
    (by simp [afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have hrev : afterRelation (fields 1) = base (fields 1) := by
    simp [afterRelation, (hfields 1).1]
  rw [hrev] at hsecond
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 1)).length + 1)]
    (some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩) =
    some ⟨some (labels .tailRead), (ambient, none), afterReverse⟩ at hsecond
  have hthird := MachineCopy.copyTrace (fields 0) row scratch
    (hfields 0).1 (hfields 0).2 hrowScratch false
    (labels .tailRead) (labels .tailRestore) (some (labels .appendOld))
    program (hprogram .tailRead) (hprogram .tailRestore) afterReverse
    (by simp [afterReverse, afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have htail : afterReverse (fields 0) = base (fields 0) := by
    simp [afterReverse, afterRelation, (hfields 0).1]
  rw [htail] at hthird
  have hfinal : Function.update afterReverse row
      (base (fields 0) ++ afterReverse row) = prefixTapes fields row base := by
    simp [afterReverse, afterRelation, prefixTapes, fieldBits, List.append_assoc]
  rw [hfinal] at hthird
  rw [show 2 * (fieldSize fields base + 3) =
    2 * ((base (fields 0)).length + 1) +
      (2 * ((base (fields 1)).length + 1) + 2 * ((base (fields 2)).length + 1)) by
        simp only [fieldSize]; omega,
    Function.iterate_add_apply,
    Function.iterate_add_apply (m := 2 * ((base (fields 1)).length + 1))
      (n := 2 * ((base (fields 2)).length + 1)), hfirst, hsecond]
  exact hthird

theorem appendTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[
        4 * fieldSize fields base + 2 * (base output).length + 9]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base output (base output ++ fieldBits fields base)⟩ := by
  have hprefix := prefixTrace fields row output scratch hfields hrowScratch
    labels exit program hprogram base hscratch ambient register
  have happend := MachineAppendAt.appendTrace row output scratch hrowOutput hrowScratch
    houtputScratch false (labels .appendOld) (labels .appendRow) (labels .appendBack)
    exit program (hprogram .appendOld) (hprogram .appendRow) (hprogram .appendBack)
    (prefixTapes fields row base)
    (by simp [prefixTapes, Ne.symm hrowScratch, hscratch]) ambient none
  have hrowbits : prefixTapes fields row base row = fieldBits fields base := by
    simp [prefixTapes, hrow]
  have hout : prefixTapes fields row base output = base output := by
    simp [prefixTapes, Ne.symm hrowOutput]
  rw [hrowbits, hout, fieldBits_length] at happend
  have hfinal : MachineAppendAt.appendTapes row output (prefixTapes fields row base) =
      Function.update base output (base output ++ fieldBits fields base) := by
    funext k
    by_cases ho : k = output
    · subst k
      simp [MachineAppendAt.appendTapes, hrowbits, hout]
    · by_cases hr : k = row
      · subst k
        simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, hrowOutput, hrow]
      · simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, ho, hr]
  rw [hfinal] at happend
  rw [show 4 * fieldSize fields base + 2 * (base output).length + 9 =
      (2 * (fieldSize fields base + (base output).length) + 3) +
        2 * (fieldSize fields base + 3) by omega,
    Function.iterate_add_apply, hprefix]
  exact happend

end MaxCutGames.Foundations.Complexity.MachineTableRows

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

abbrev Buffer := MachineFixedBlockMap.Buffer 4096
abbrev State (σ : Type) := (σ × Buffer) × Option Bool

def zeroBuffer : Buffer := MachineFixedBlockMap.emptyBuffer 4096

def copyStateEquiv (σ : Type) : ((σ × Option Bool) × Buffer) ≃ State σ where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

inductive Label
  | lookup (label : MachineAffineLookup.Label)
  | copyRelation | reverseSeed | reverseScan | reverseRestore
  | emit (label : MachineTableRows.Label)
  deriving DecidableEq, Fintype

def relationCopyAt {K σ Λ : Type} (src dst : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineStateEquiv.statement (copyStateEquiv σ)
    (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace MaxCutGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

inductive Label
  | owner (l : MachineAffineLookup.Label)
  | ownerClearQuery | ownerClearWork
  | copyXFirst | copyXSecond | copyOwnerFirst | copyOwnerSecond | rankInit
  | rank (l : MachineCloudRank.RankLabel)
  | rankClearQuery | rankClearWork | rankClearFuel
  | prefixCode (l : MachineCloudPrefix.Label)
  | prefixClearQuery | prefixClearFuel
  | cloud (l : MachineCloudPadding.Label)
  deriving DecidableEq, Fintype

def prefixTape : MachineCloudPrefix.Tape → Tape
  | .inner .table => .inl 0
  | .inner .query => .inl 9
  | .inner .count => .inl 10
  | .inner .work => .inl 11
  | .inner .scratch => .inl 12
  | .inner .spare => .inl 13
  | .inner .power => .inl 14
  | .inner .level => .inl 15
  | .inner .fuel => .inl 16
  | .inner .product => .inl 17
  | .bound => .inl 2
  | .remaining => .inl 18
  | .total => .inl 5

def cloudTape : MachineCloudPadding.Tape → Tape
  | .table => .inl 0
  | .query => .inl 2
  | .count => .inl 4
  | .work => .inl 9
  | .scratch => .inl 10
  | .spare => .inl 11
  | .power => .inr .padding
  | .level => .inr .level
  | .fuel => .inl 12
  | .product => .inl 13

variable {σ : Type}

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl i => match i.val with
    | 0 => some (.inner .table)
    | 9 => some (.inner .query)
    | 10 => some (.inner .count)
    | 11 => some (.inner .work)
    | 12 => some (.inner .scratch)
    | 13 => some (.inner .spare)
    | 14 => some (.inner .power)
    | 15 => some (.inner .level)
    | 16 => some (.inner .fuel)
    | 17 => some (.inner .product)
    | 2 => some .bound
    | 18 => some .remaining
    | 5 => some .total
    | _ => none
  | .inr _ => none

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (prefixTape k) = some k := by
  cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : prefixTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [prefixView, prefixTape] <;> subst k <;> rfl
  | inr j => simp_all [prefixView]

theorem cloudView_left (k : MachineCloudPadding.Tape) : cloudView (cloudTape k) = some k := by
  cases k <;> rfl
theorem cloudView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : cloudView j = some k) : cloudTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [cloudView, cloudTape] <;> subst k <;> rfl
  | inr j => cases j <;> simp_all [cloudView, cloudTape] <;> subst k <;> rfl

def cfg (label : Option Label) (data : Data) (ambient : σ) (register : Option Bool) :
    TM2.Cfg Alphabet Label (State σ) :=
  ⟨label, ((ambient, false), register), frame data⟩

def rankQuery (v x : Nat) : List Bool := MachineCloudRank.queryWord v x []

def queryFrame (data : Data) (v x : Nat) : Tape → List Bool :=
  Function.update (Function.update (frame data) (.inl 9) (rankQuery v x))
    (.inl 3) (encodeWord 0)

end MaxCutGames.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace MaxCutGames.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

abbrev BaseAlphabet := MachineCloudCount.Alphabet

variable {σ : Type}

def baseProgram : BaseLabel → TM2.Stmt BaseAlphabet BaseLabel (BaseState σ)
  | .queryFirst => Reduction.MachineTransfer.loopAt .target .scratch id false
      .queryFirst (some .querySecond)
  | .querySecond => MachineCopy.forkLoop .scratch .target .spare false
      .querySecond (some .querySkip)
  | .querySkip => MachineLookup.discard .spare .querySkip .tableFirst
  | .tableFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .tableFirst (some .tableSecond)
  | .tableSecond => MachineCopy.forkLoop .scratch .original .work false
      .tableSecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .field
  | .field => MachineCloudCount.fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .target id false
      .restore (some .done)
  | .skip i => MachineLookup.discard .work (.skip i) (skipLabel (i.val + 1))
  | .clearWork => MachineDrain.drain .work .clearWork (some .clearRank)
  | .clearRank => MachineDrain.drain .spare .clearRank (some .done)
  | .done => .halt

theorem baseProgram_skip {i : Nat} (hi : i < 4097) :
    baseProgram (σ := σ) (skipLabel i) =
      MachineLookup.discard .work (skipLabel i) (skipLabel (i + 1)) := by
  simp only [skipLabel, dite_eq_left hi, baseProgram]

abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet BaseAlphabet (fun _ : Unit => Bool)

def go (phase : Phase) (label : Label) : TM2.Stmt Alphabet Label (State σ) :=
  .load (fun s => ((s.1.1, none), phase)) (.goto fun _ => label)

/-- Pop the one-bit match result. Only a match pops the remaining local
rank. Every completed skipped row separately pushes the global position. -/
def dispatcher : TM2.Stmt Alphabet Label (State σ) :=
  .branch (fun s => decide (s.2 = .checking))
    (.pop (.inl .count) (fun s bit => ((s.1.1, bit), s.2))
      (.branch (fun s => s.1.2.getD false)
        (.pop (.inl .spare) (fun s bit => ((s.1.1, bit), s.2))
          (.branch (fun s => s.1.2.getD false)
            (go .advancing (.inl (skipLabel 0)))
            (go .finishing (.inl .clearWork))))
        (go .advancing (.inl (skipLabel 0)))))
    (.branch (fun s => decide (s.2 = .advancing))
      (.push (.inr ()) (fun _ => true) (go .checking (.inl .field)))
      (.load (fun s => ((s.1.1, none), Phase.checking)) .halt))

def extra : Control → TM2.Stmt Alphabet Label (State σ)
  | .initialize_ => .push (.inr ()) (fun _ => false) (go .checking (.inl .queryFirst))
  | .dispatch => dispatcher

def program : Label → TM2.Stmt Alphabet Label (State σ) :=
  MachineEmbedding.program (some (.inr .dispatch)) baseProgram extra

def memory (original work target scratch hit rank position : List Bool) :
    ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineCloudCount.memory original work target scratch hit rank)
    (fun _ : Unit => position)

@[simp] theorem memory_inl (a b c d e f g : List Bool) (k : BaseTape) :
    memory a b c d e f g (.inl k) = MachineCloudCount.memory a b c d e f k := rfl
@[simp] theorem memory_position (a b c d e f g : List Bool) :
    memory a b c d e f g (.inr ()) = g := rfl

@[simp] theorem update_memory_hit (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inl .count) x = memory a b c d x f g := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl
@[simp] theorem update_memory_rank (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inl .spare) x = memory a b c d e x g := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl
@[simp] theorem update_memory_position (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inr ()) x = memory a b c d e f x := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

def cfg (label : Option Label) (phase : Phase)
    (original work target hit rank position : List Bool)
    (ambient : σ) (register : Option Bool) : TM2.Cfg Alphabet Label (State σ) :=
  ⟨label, (((ambient, false), register), phase), memory original work target [] hit rank position⟩

theorem liftTrace (phase : Phase) (position : List Bool) (n : Nat)
    (a b : TM2.Cfg BaseAlphabet BaseLabel (BaseState σ))
    (h : (advance (TM2.step baseProgram))^[n] (some a) = some b) :
    (advance (TM2.step (program (σ := σ))))^[n]
      (some (MachineEmbedding.configuration (some (.inr .dispatch)) phase
        (fun _ : Unit => position) a)) =
      some (MachineEmbedding.configuration (some (.inr .dispatch)) phase
        (fun _ : Unit => position) b) :=
  liftSuccessfulTrace (TM2.step baseProgram) (TM2.step program)
    (MachineEmbedding.configuration (some (.inr .dispatch)) phase (fun _ : Unit => position))
    (MachineEmbedding.step_simulation (some (.inr .dispatch)) phase
      (fun _ : Unit => position) baseProgram extra) n a b h

theorem compareTrace (original suffix targetSuffix rank position : List Bool)
    (x v : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[x + min x v + 3]
      (some (cfg (some (.inl .field)) .checking original (encodeWord x ++ suffix)
        (encodeWord v ++ targetSuffix) [] rank position ambient register)) =
      some (cfg (some (.inr .dispatch)) .checking original suffix
        (encodeWord v ++ targetSuffix) (List.replicate (if x = v then 1 else 0) true)
        rank position ambient none) := by
  have h := MachineCloudCount.preservingFieldTrace BaseLabel.field BaseLabel.restore BaseLabel.done
    baseProgram rfl rfl original suffix targetSuffix [] rank x v ambient register
  simp only [List.append_nil] at h
  have hhalt : (advance (TM2.step baseProgram))^[x + min x v + 3]
      (some ⟨some .field, ((ambient, false), register),
        MachineCloudCount.memory original (encodeWord x ++ suffix)
          (encodeWord v ++ targetSuffix) [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true) rank⟩ := by
    rw [show x + min x v + 3 = (x + min x v + 2) + 1 by omega,
      Function.iterate_succ_apply', h, advance_some]
    rfl
  convert liftTrace Phase.checking position _ _ _ hhalt using 1 <;> rfl

theorem dispatch_miss (original work target rank position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [] rank position ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing
        original work target [] rank position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step, cfg]

theorem dispatch_hit_succ (original work target rankSuffix position : List Bool)
    (rank : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord (rank + 1) ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original work target []
        (encodeWord rank ++ rankSuffix) position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem dispatch_hit_zero (original work target rankSuffix position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord 0 ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rankSuffix position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord]

theorem advanceStep (original work target rank positionSuffix : List Bool)
    (position : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .advancing original work target []
      rank (encodeWord position ++ positionSuffix) ambient none) =
      some (cfg (some (.inl .field)) .checking original work target []
        rank (encodeWord (position + 1) ++ positionSuffix) ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem finishStep (original target position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .finishing
      original [] target [] [] position ambient none) =
      some (cfg none .checking original [] target [] [] position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step, cfg]

theorem initializeStep (original target output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program (cfg (some (.inr .initialize_)) .checking
      original [] target [] [] output ambient register) =
      some (cfg (some (.inl .queryFirst)) .checking
        original [] target [] [] (encodeWord 0 ++ output) ambient none) := by
  simp [program, MachineEmbedding.program, extra, go, TM2.stepAux, TM2.step, cfg, encodeWord]

def prefixTime (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => prefixTime v rs + (rowTime v r + 3)

/-- Both copied workspaces are physically drained after finding the row;
the original table, complete query, and position output are retained. -/
theorem cleanupTrace (original work target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[work.length + rank.length + 4]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg none .checking original [] target [] [] position ambient none) := by
  have hwork := MachineDrain.drainTrace MachineCloudCount.Tape.work BaseLabel.clearWork (some BaseLabel.clearRank)
    baseProgram rfl (MachineCloudCount.memory original work target [] [] rank) work
    (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hwork
  have hrank := MachineDrain.drainTrace MachineCloudCount.Tape.spare BaseLabel.clearRank (some BaseLabel.done)
    baseProgram rfl (MachineCloudCount.memory original [] target [] [] rank) rank
    (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hrank
  have raw : (advance (TM2.step baseProgram))^[work.length + rank.length + 3]
      (some ⟨some .clearWork, ((ambient, false), none),
        MachineCloudCount.memory original work target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original [] target [] [] []⟩ := by
    rw [show work.length + rank.length + 3 =
        1 + ((rank.length + 1) + (work.length + 1)) by omega,
      Function.iterate_add_apply _ 1, Function.iterate_add_apply _ (rank.length + 1),
      hwork, hrank, Function.iterate_one, advance_some]
    rfl
  have lifted := liftTrace Phase.finishing position _ _ _ raw
  have h : (advance (TM2.step program))^[work.length + rank.length + 3]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .finishing
        original [] target [] [] position ambient none) := by
    convert lifted using 1 <;> rfl
  rw [show work.length + rank.length + 4 = (work.length + rank.length + 3) + 1 by omega,
    Function.iterate_succ_apply', h, advance_some]
  exact finishStep original target position ambient

theorem selectedTrace (v : Nat) (original work targetSuffix rankSuffix position : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original (encodeWord v ++ work)
        (encodeWord v ++ targetSuffix) [] (encodeWord 0 ++ rankSuffix) position ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] [] position ambient none) := by
  have hcompare := compareTrace original work targetSuffix (encodeWord 0 ++ rankSuffix)
    position v v ambient register
  simp only [ite_true, if_true, List.replicate_succ, List.replicate_zero] at hcompare
  rw [show 2 * v + work.length + rankSuffix.length + 8 =
      (work.length + rankSuffix.length + 4) + (1 + (v + min v v + 3)) by
        simp only [Nat.min_self]; omega,
    Function.iterate_add_apply _ (work.length + rankSuffix.length + 4),
    Function.iterate_add_apply _ 1, hcompare, Function.iterate_one, advance_some,
    dispatch_hit_zero]
  exact cleanupTrace original work (encodeWord v ++ targetSuffix) rankSuffix position ambient

abbrev queryWord := MachineCloudRank.queryWord

def prepareSteps (n m v rank : Nat) (rs : List Row) (querySuffix : List Bool) : Nat :=
  2 * ((queryWord v rank querySuffix).length + 1) + (v + 1) +
    2 * ((MachineCloudCount.inputWord n m rs).length + 1) + (n + 1) + (m + 1)

def totalSteps (n m v rank : Nat) (rs preceding : List Row)
    (work querySuffix : List Bool) : Nat :=
  prepareSteps n m v rank rs querySuffix + prefixTime v preceding +
    2 * v + work.length + querySuffix.length + 9

open MaxCutGames.Foundations.PCP

end MaxCutGames.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Static, pointwise Boolean presentation of the actual family tape alphabet.
Every conversion below is an identity on symbols and has no machine runtime. -/

/-!
# Actual family-table installation and counter cleanup

Checked physical drain and transfer loops are placed in the family program
through its finite register equivalence. Alphabet equality transports their
actual traces back to the dependent alphabet of the full family machine.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem controlDrainTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source : K) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (MachineDrain.drain source again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none), Function.update base source []⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = MachineDrain.drain source again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := MachineDrain.drainTrace source again exit raw atRaw base (base source) ambient register
  simp only [Function.update_eq_self] at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id] using
    controlTrace states target ((base source).length + 1) _ _ run

theorem controlTransferTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source destination : K)
    (distinct : source ≠ destination) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (Reduction.MachineTransfer.loopAt source destination id false again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none),
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = Reduction.MachineTransfer.loopAt source destination id false again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := Reduction.MachineTransfer.transferAt_fromTapes source destination distinct id false
    again exit raw atRaw base ambient register
  unfold Reduction.MachineTransfer.nextAt at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id,
    List.map_id] using controlTrace states target ((base source).length + 1) _ _ run

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingInternalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.PreprocessingInternalRows

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- The one actual cloud-table lookup used by this internal row. -/
def localStep (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (cloudSize t v + padding v) × Fin q :=
  ExpanderTables.lookup (tables v) (paddedCloudRank t padding v x, p)

/-- Decode the returned cloud index into its actual global padded dart. -/
def destination (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PaddedCloud t padding v :=
  paddedCloudSelect t padding v (localStep t padding tables v x p).1

def rowIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (vertexCount t padding * (q + 1)) :=
  PortTables.rowIndex (vertexCount t padding) (q + 1)
    (vertexOrder t padding x.val, portOrder q (.inl p))

/-- This is a row read from the actual serialized output table. -/
def row (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[rowIndex t padding v x p]

/-- The fixed, complete 64-label equality predicate. -/
def equalityRelation : GraphTables.RelationTable :=
  GraphTables.relationOf (fun a b => decide (a = b))

@[simp] theorem equalityRelation_apply (a b : GraphTables.Label) :
    GraphTables.relationAt equalityRelation a b = decide (a = b) :=
  GraphTables.relationAt_relationOf _ a b

/-- The reindexed local cloud graph is exactly the stored local lookup. -/
theorem cloud_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (cloudGraphs t padding tables v).rot (x, p) =
      (destination t padding tables v x p, (localStep t padding tables v x p).2) := by
  have h := GraphTransport.reindex_rot (ExpanderTables.graph (tables v))
    (paddedCloudEquiv t padding v).symm (Equiv.refl _)
    (paddedCloudRank t padding v x) p
  simpa only [cloudGraphs, ExpanderTables.graph_rot, Equiv.refl_apply,
    paddedCloudRank, paddedCloudSelect, Equiv.symm_apply_apply, destination, localStep] using h

/-- The actual global replacement rotation uses that same lookup and select. -/
theorem source_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (sourcePortGraph t padding tables).rot (x.val, .inl p) =
      ((destination t padding tables v x p).val,
        .inl (localStep t padding tables v x p).2) := by
  rcases x with ⟨x, hx⟩
  subst v
  exact congrArg
    (fun z : PaddedCloud t padding
        ((paddedGraph (GraphTables.semantics t) (fun v => Fin (padding v))).tail x) × Fin q =>
      (z.1.val, (Sum.inl z.2 : Fin q ⊕ Unit)))
    (cloud_rotation t padding tables _ ⟨x, rfl⟩ p)

/-- Full output rotation, retaining the actual return port. -/
theorem rotation_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding x.val, portOrder q (.inl p)) =
      (vertexOrder t padding (destination t padding tables v x p).val,
        portOrder q (.inl (localStep t padding tables v x p).2)) := by
  rw [rotation_ofCloudTables, source_rotation t padding tables v x p]

/-- The stored global reverse index is the row-major encoding of the destination. -/
theorem reverseIndex_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    ((ofCloudTables t padding tables).reverseIndex[rowIndex t padding v x p]).val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  unfold rowIndex
  rw [← PortTables.rowIndex_rotation, rotation_internal t padding tables v x p,
    PortTables.rowIndex_val, portOrder_internal]
  dsimp only
  omega

theorem relation_ext_inline_PreprocessingInternalRows {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

/-- Equality is the entire stored relation vector, not only one tested entry. -/
theorem relations_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (ofCloudTables t padding tables).relations[rowIndex t padding v x p] = equalityRelation := by
  apply relation_ext_inline_PreprocessingInternalRows
  intro a b
  rw [equalityRelation_apply]
  exact accepts_internal t padding tables x.val p a b

@[simp] theorem row_tail (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).tail.val = (vertexOrder t padding x.val).val := by
  simp only [row, rowIndex, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

theorem row_reverse (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    reverseIndex_internal t padding tables v x p

@[simp] theorem row_relation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).relation = equalityRelation := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    relations_internal t padding tables v x p

@[simp] theorem localStep_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    localStep t padding tables v (paddedOld t padding v x) p =
      ExpanderTables.lookup (tables v) (Fin.castAdd (padding v) (cloudRank t v x), p) := rfl

@[simp] theorem localStep_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    localStep t padding tables v (paddedNew t padding v j) p =
      ExpanderTables.lookup (tables v) (Fin.natAdd (cloudSize t v) j, p) := rfl

@[simp] theorem row_tail_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    (row t padding tables v (paddedOld t padding v x) p).tail.val = x.val.val := by
  rw [row_tail]
  rfl

@[simp] theorem row_tail_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    (row t padding tables v (paddedNew t padding v j) p).tail.val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val := by
  rw [row_tail]
  exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j

/-- The global target number computed from an arbitrary returned cloud index. -/
def selectedIndex (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) : Nat :=
  if hi : i.val < cloudSize t v then
    (cloudSelect t v ⟨i.val, hi⟩).val.val
  else t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v)

/-- Rank/select destination decoding agrees with the prefix-offset formula. -/
theorem selectedIndex_eq (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    (vertexOrder t padding (paddedCloudSelect t padding v i).val).val =
      selectedIndex t padding v i := by
  unfold selectedIndex
  split
  · rename_i hi
    have he : i = Fin.castAdd (padding v) (⟨i.val, hi⟩ : Fin (cloudSize t v)) := Fin.ext rfl
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_castAdd]
    rfl
  · rename_i hi
    have hj : i.val - cloudSize t v < padding v := by have h := i.isLt; omega
    have he : i = Fin.natAdd (cloudSize t v) (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v)) := by
      apply Fin.ext
      dsimp only [Fin.val_natAdd]
      omega
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_natAdd]
    change (vertexOrder t padding
      (Sum.inr ⟨v, (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v))⟩)).val = _
    exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v _

/-- Old target indices select the original dart from its actual cloud list. -/
theorem selectedIndex_old (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : i.val < cloudSize t v) :
    selectedIndex t padding v i = (cloudSelect t v ⟨i.val, hi⟩).val.val := by
  simp only [selectedIndex, dite_eq_left hi]

/-- Dummy target indices use the checked prefix offset and local index. -/
theorem selectedIndex_dummy (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : cloudSize t v ≤ i.val) :
    selectedIndex t padding v i =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v) := by
  simp only [selectedIndex, dite_eq_right (Nat.not_lt_of_ge hi)]

/-- Closed arithmetic reverse field for the row machine. -/
theorem row_reverse_selectedIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * selectedIndex t padding v (localStep t padding tables v x p).1 +
        (localStep t padding tables v x p).2.val := by
  rw [row_reverse]
  unfold destination
  rw [selectedIndex_eq]

end MaxCutGames.Foundations.PCP.PreprocessingInternalRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Alphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical construction of an internal regularization row

The input values belong on unary tapes. The cloud degree and the queried port
are the only arithmetic parameters fixed in finite control. The stored cloud
rotation supplies both the destination's local index and the return port.
The final row contains the full fixed equality predicate.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

inductive RotorLabel (q : Nat)
  | lookup (stage : MachineAffineLookup.Label)
  | initialize_ | divide | emit (r : Fin q)
  deriving DecidableEq, Fintype

abbrev SelectTape := MachineCloudSelect.Tape ⊕ SelectExtraTape
abbrev RawSelectAlphabet : SelectTape → Type :=
  MachineEmbedding.Alphabet MachineCloudSelect.Alphabet (fun _ : SelectExtraTape => Bool)
abbrev SelectAlphabet (_ : SelectTape) := Bool

theorem selectAlphabet_eq : RawSelectAlphabet = SelectAlphabet := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

def selectToBoolWord : (k : SelectTape) → List (RawSelectAlphabet k) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def selectToBoolTapes (base : ∀ k, List (RawSelectAlphabet k)) : SelectTape → List Bool :=
  fun k => selectToBoolWord k (base k)

def selectScratch : SelectTape := .inl (.inl .scratch)
def selectQuery : SelectTape := .inl (.inl .target)
def selectOutput : SelectTape := .inl (.inr ())

def compareSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localIndex, .inr .cloudSize, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def subtractSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def copySource : SelectCopy → SelectTape
  | .oldLocal | .dummyLocal => .inr .localIndex
  | .oldOwner => .inr .owner
  | .dummySize => .inr .cloudSize
  | .dummyDifference => .inr .localWork

def copyDestination : SelectCopy → SelectTape
  | .oldLocal | .oldOwner => selectQuery
  | .dummyLocal => .inr .localWork
  | .dummySize => .inr .sizeWork
  | .dummyDifference => selectOutput

def addSource : SelectAdd → SelectTape
  | .prefixOffset => .inr .prefixOffset
  | .darts => .inr .darts

def cleanupTape (i : Fin 5) : SelectTape :=
  ![selectQuery, .inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i

abbrev CoreState (σ : Type) (q : Nat) :=
  (σ × (MachineFixedBlockMap.Buffer 4096 ×
    (Fin q × (Bool × MachineCloudSelect.Phase)))) × Option Bool

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_SelectorMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]

def coreInitialState (q : Nat) (positive : 0 < q) (ambient : σ) : CoreState σ q :=
  ((ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking)))), none)

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

abbrev State := MachineRegularOriginalRow.State

inductive Label
  | row (label : MachineRegularOriginalRow.Label)
  | query | scan | rawReverse | computedReverse | relation
  deriving DecidableEq, Fintype

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineDummyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

/-- The actual 64-by-64 always-accepting relation. -/
def trueRelation : RelationTable := Vector.replicate 4096 true

end MaxCutGames.Foundations.Complexity.MachineDummyRows

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularDummyRow

open Turing MachineComposition PCP.GraphTables

structure Input (x : Nat) (base : Tape → List Bool) : Prop where
  source : base 0 = encodeWord x
  reverseEmpty : base 1 = []
  relationEmpty : base 2 = []
  scratchEmpty : base 3 = []
  rowEmpty : base 5 = []

def memory (x : Nat) (output : List Bool) : Tape → List Bool :=
  ![encodeWord x, [], [], [], output, []]

theorem memory_input (x : Nat) (output : List Bool) : Input x (memory x output) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end MaxCutGames.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

/-- Split any indexed list at the actual old/new vertex boundary. -/
theorem ofFn_split {α : Type*} (h : n ≤ m) (f : Fin m → α) :
    List.ofFn f =
      List.ofFn (fun v : Fin n => f (v.castLE h)) ++
        List.ofFn (fun v : Fin (m - n) => f (PreprocessingPaddingTables.vertexEquiv h (.inr v))) := by
  calc
    List.ofFn f = List.ofFn
        (fun v : Fin (n + (m - n)) => f (Fin.cast (Nat.add_sub_of_le h) v)) :=
      List.ofFn_congr (Nat.add_sub_of_le h).symm f
    _ = _ := by rw [List.ofFn_add]; rfl

end MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

theorem relation_ext_inline_PreprocessingRegularWords {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

end MaxCutGames.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularVertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

def originalStateEquiv (σ : Type) (q : Nat) :
    MachineRegularOriginalClean.State (σ × (Fin q × (Bool × MachineCloudSelect.Phase))) ≃
      CoreState σ q where
  toFun s := ((s.1.1.1, (s.1.2, s.1.1.2)), s.2)
  invFun s := (((s.1.1, s.1.2.2), s.1.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨a,b⟩,c⟩,d⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,c⟩⟩,d⟩; rfl

theorem dummyMemory_update (x : Nat) (output output' : List Bool) :
    Function.update (MachineRegularDummyRow.memory x output)
      (4 : MachineRegularDummyRow.Tape) output' = MachineRegularDummyRow.memory x output' := by
  funext j; fin_cases j <;> rfl

end MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

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

abbrev CoreState := MachineRegularInternalRow.CoreState Unit internalDegree
abbrev Data := MachineRegularMetadata.Data
abbrev BaseTable := PreprocessingRegularTables.BaseTable

def coreFrame (data : Data) (i : Fin 27) : List Bool :=
  MachineRegularMetadata.frame data (.inl i)

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOwnerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev Data := MachineRegularMetadata.Data
abbrev CoreState := MachineRegularOriginalBody.CoreState
abbrev BaseTable := PreprocessingRegularTables.BaseTable

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Header

abbrev Tape := MachineCloudPrefix.Tape ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool

def tableTape : Tape := .inl (.inner .table)
def nTape : Tape := .inl .bound
def queryTape : Tape := .inl (.inner .query)
def fuelTape : Tape := .inl .remaining
def sumTape : Tape := .inl .total
def mTape : Tape := .inr .m
def indexTape : Tape := .inr .index
def workTape : Tape := .inr .work
def scratchTape : Tape := .inr .scratch
def verticesTape : Tape := .inr .vertices
def dartsTape : Tape := .inr .darts
def emitTape : Tape := .inr .emit
def outputTape : Tape := .inr .output

def memory (inner : MachineCloudPrefix.Tape → List Bool)
    (m index work scratch vertices darts emit output : List Bool) : Tape → List Bool
  | .inl k => inner k
  | .inr .m => m
  | .inr .index => index
  | .inr .work => work
  | .inr .scratch => scratch
  | .inr .vertices => vertices
  | .inr .darts => darts
  | .inr .emit => emit
  | .inr .output => output

def frame (t n v f s m i w a N R e o : List Bool) : Tape → List Bool :=
  memory (MachineCloudPrefix.frame t v [] [] [] n f s) m i w a N R e o

@[simp] theorem frame_table (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o tableTape = t := rfl
@[simp] theorem frame_n (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o nTape = n := rfl
@[simp] theorem frame_query (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o queryTape = v := rfl
@[simp] theorem frame_fuel (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o fuelTape = f := rfl
@[simp] theorem frame_sum (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o sumTape = s := rfl
@[simp] theorem frame_m (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o mTape = m := rfl
@[simp] theorem frame_index (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o indexTape = i := rfl
@[simp] theorem frame_work (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o workTape = w := rfl
@[simp] theorem frame_scratch (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o scratchTape = a := rfl
@[simp] theorem frame_vertices (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o verticesTape = N := rfl
@[simp] theorem frame_darts (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o dartsTape = R := rfl
@[simp] theorem frame_emit (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o emitTape = e := rfl
@[simp] theorem frame_output (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o outputTape = o := rfl

@[simp] theorem update_frame_table (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) tableTape x =
      frame x n v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_n (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) nTape x =
      frame t x v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_query (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) queryTape x =
      frame t n x f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_fuel (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) fuelTape x =
      frame t n v x s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_sum (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) sumTape x =
      frame t n v f x m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_m (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) mTape x =
      frame t n v f s x i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_index (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) indexTape x =
      frame t n v f s m x w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_work (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) workTape x =
      frame t n v f s m i x a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_scratch (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) scratchTape x =
      frame t n v f s m i w x N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_vertices (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) verticesTape x =
      frame t n v f s m i w a x R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_darts (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) dartsTape x =
      frame t n v f s m i w a N x e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_emit (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) emitTape x =
      frame t n v f s m i w a N R x o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_output (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) outputTape x =
      frame t n v f s m i w a N R e x := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

def fieldTape : Field → Tape
  | .vertices => nTape
  | .darts => mTape

def lookupSlots (field : Field) : Fin 5 → Tape :=
  ![tableTape, indexTape, workTape, fieldTape field, scratchTape]

theorem lookupSlots_injective (field : Field) : Function.Injective (lookupSlots field) := by
  intro i j h
  cases field <;> fin_cases i <;> fin_cases j <;>
    simp_all [lookupSlots, fieldTape, tableTape, indexTape, workTape, nTape, mTape, scratchTape]

def copySource : CopyPhase → Tape
  | .count => mTape
  | .rEmit => dartsTape
  | .nEmit => verticesTape

def copyDestination : CopyPhase → Tape
  | .count => verticesTape
  | .rEmit | .nEmit => emitTape

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl k => some k
  | .inr _ => none

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (.inl k) = some k := rfl

theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : Sum.inl k = j := by
  cases j <;> simp_all [prefixView]

theorem prefixTapes (inner : MachineCloudPrefix.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes prefixView inner extra =
      memory inner (extra mTape) (extra indexTape) (extra workTape) (extra scratchTape)
        (extra verticesTape) (extra dartsTape) (extra emitTape) (extra outputTape) := by
  funext j
  cases j with
  | inl k => rfl
  | inr k => cases k <;> rfl

end Header

namespace Top

abbrev BaseTable := PreprocessingRegularTables.BaseTable

end Top
end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Subdivision
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The four-edge subdivision.
Every input occurrence has its own three interior vertices, even when
the original endpoints coincide or another occurrence has the same endpoints.
The left/right presentation inverts the permutation on the fourth edge.
-/

namespace MaxCutGames.Explicit

open scoped BigOperators

namespace Subdivision

variable {V E A : Type*}

variable [DecidableEq A]

theorem count_on_occurrence_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i) (a ((game g).left (e, i))) =
        b ((game g).right (e, i)) then 1 else 0) ≤
      3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  exact local_count_le (g.permutation e)
      (a (Sum.inl (g.source e))) (b (e, false)) (a (Sum.inr e))
      (b (e, true)) (a (Sum.inl (g.target e)))

theorem count_on_occurrence_extend (g : OccurrenceGame V E A) (a : V → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i)
      (extendLeft g a ((game g).left (e, i))) =
        extendRight g a ((game g).right (e, i)) then 1 else 0) =
      3 + (if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  simpa [game, permutation, left, right, extendLeft, extendRight] using
    local_count_extend (g.permutation e) (a (g.source e)) (a (g.target e))

variable [Fintype E]

theorem satisfiedCount_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) :
    (game g).satisfiedCount a b ≤
      3 * Fintype.card E + g.satisfiedCount (restrict a) := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ e, (3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat)) :=
      Finset.sum_le_sum (fun e _ => count_on_occurrence_le g a b e)
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

/-- Fresh interiors can be assigned independently, so the upper bound is attained. -/
theorem satisfiedCount_extend (g : OccurrenceGame V E A) (a : V → A) :
    (game g).satisfiedCount (extendLeft g a) (extendRight g a) =
      3 * Fintype.card E + g.satisfiedCount a := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  simp_rw [count_on_occurrence_extend]
  simp [Finset.sum_add_distrib, Nat.mul_comm]

variable [Fintype V] [Fintype A] [Nonempty A]

theorem maxSatisfied_eq (g : OccurrenceGame V E A) :
    (game g).maxSatisfied = 3 * Fintype.card E + g.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro ab _
    exact (satisfiedCount_le g ab.1 ab.2).trans
      (Nat.add_le_add_left (g.satisfiedCount_le_maxSatisfied (restrict ab.1)) _)
  · obtain ⟨a, ha⟩ := g.maxSatisfied_attained
    rw [← ha, ← satisfiedCount_extend]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

theorem value_eq [Nonempty E] (g : OccurrenceGame V E A) :
    (game g).value = 1 - (1 - g.value) / 4 := by
  have hE : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [BipartiteGame.value, maxSatisfied_eq, edge_count, OccurrenceGame.value]
  push_cast
  field_simp [hE]
  ring

end Subdivision

end MaxCutGames.Explicit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingLazyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact codec expansion of the executable lazy graph table. Each vertex
contributes its `d` always-accepting selfloops, followed by its `d` stored
constraints with the reverse field changed by the displayed div/mod map. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open MaxCutGames.Foundations.Complexity

variable {n d : Nat}

theorem relation_ext_inline_PreprocessingLazyWords {r s : RelationTable}
    (h : ∀ a b, relationAt r a b = relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [relationAt, Prod.eta, Equiv.apply_symm_apply, Fin.getElem_fin] using
    h (relationIndex.symm ⟨i, hi⟩).1 (relationIndex.symm ⟨i, hi⟩).2

end MaxCutGames.Foundations.PCP.PreprocessingLazyWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap )

variable {K Λ A : Type} [DecidableEq K]

abbrev Buffer := MachineRegularOriginalRow.Buffer

end MaxCutGames.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingOverlayWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stored-row and codec expansion of the executable overlay. Within
each vertex block, all original ports precede all expander ports. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

theorem relation_ext_inline_PreprocessingOverlayWords {r s : RelationTable}
    (h : ∀ a b, relationAt r a b = relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [relationAt, Prod.eta, Equiv.apply_symm_apply, Fin.getElem_fin] using
    h (relationIndex.symm ⟨i, hi⟩).1 (relationIndex.symm ⟨i, hi⟩).2

end MaxCutGames.Foundations.PCP.PreprocessingOverlayWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingStageMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable, codec-compatible stage maps for the actual preprocessing
constructor. The decomposition below is an equality of its existing functions;
runtime certificates must be supplied by the respective concrete machines. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

abbrev BaseTable := PreprocessingTables.BaseTable

end MaxCutGames.Foundations.PCP.PreprocessingStageMaps

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

def initialTapes (input : List Bool) : Tape → List Bool := tapes input [] [] []

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

namespace MaxCutGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open MaxCutGames.Foundations.PCP
open MachineCloudPadding

def subtractTape : MachineCloudPadding.Tape → Tape
  | .table => .original
  | .query => .output
  | .count => .vertex
  | .work => .work
  | .scratch => .saved
  | .spare => .scratch
  | .power => .fuel
  | .level => .level
  | .fuel => .product
  | .product => .rowSpare
def subtractView : Tape → Option MachineCloudPadding.Tape
  | .original => some .table
  | .output => some .query
  | .vertex => some .count
  | .work => some .work
  | .saved => some .scratch
  | .scratch => some .spare
  | .fuel => some .power
  | .level => some .level
  | .product => some .fuel
  | .rowSpare => some .product
  | _ => none

theorem subtractView_left (k : MachineCloudPadding.Tape) :
    subtractView (subtractTape k) = some k := by cases k <;> rfl
theorem subtractView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : subtractView j = some k) : subtractTape k = j := by
  cases j <;> cases k <;> simp_all [subtractView, subtractTape]

theorem subtractTapes (input output vertex edge power level fuel : List Bool) :
    Placement.tapes subtractView
      (MachineCloudPadding.memory input output vertex [] [] [] fuel level [] [])
      (memory [] [] [] edge power [] [] []) =
      memory input output vertex edge power level fuel [] := by
  funext k; cases k <;> rfl

theorem frameTrace_inline_MachineVertexPadding {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ) (n : Nat)
    (a b : TM2.Cfg Γ Λ σ) (run : (advance (TM2.step source))^[n] (some a) = some b) :
    (advance (TM2.step (MachineStateFrame.frameProgram source)))^[n]
      (some (MachineStateFrame.frameConfiguration ambient a)) =
      some (MachineStateFrame.frameConfiguration ambient b) := by
  have h := MachineStateFrame.frame_iterate source ambient n (some a)
  simpa only [Option.map_some, run] using h

end MaxCutGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineOverlayTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineOverlayTable

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type} {d e : Nat}

abbrev Ambient (A : Type) (d e : Nat) := ((A × Fin e) × MachineLazyRows.Buffer) × Fin d
abbrev State (A : Type) (d e : Nat) := Ambient A d e × Option Bool

def initialTapes (graph rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.initialTapes graph) rawH

theorem placedTapes (left : Fin 5 → List Bool) (rawH : List Bool) :
    Placement.tapes splitView left (initialTapes [] rawH) = combine left rawH := by
  funext k
  cases k <;> rfl

end MaxCutGames.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedOverlay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

abbrev BaseTable := PreprocessingStageMaps.BaseTable

end MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

/-! Exact dummy-block codec used by the complete lazy-table machine. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTableRuntime
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

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

def program : Label → TM2.Stmt Alphabet Label State
  | .inl l => clockStatement (MachineLogCounter.program l)
  | .inr .copyFirst => Reduction.MachineTransfer.loopAt (.inr .input) (.inr .scratch)
      id false (.inr .copyFirst) (some (.inr .copySecond))
  | .inr .copySecond => MachineCopy.forkLoop (.inr .scratch) (.inr .input) (.inr .archive)
      false (.inr .copySecond) (some (.inr .seed))
  | .inr .seed => .push (.inl 0) (fun _ => false) (.goto fun _ => .inr .headerFirst)
  | .inr .headerFirst => readHeader (.inr .headerFirst) (.inr .headerSecond)
  | .inr .headerSecond => readHeader (.inr .headerSecond) (.inl 0)
  | .inr .clearInput => MachineDrain.drain (.inr .input) (.inr .clearInput)
      (some (.inr .clockCopy))
  | .inr .clockCopy => Reduction.MachineTransfer.loopAt (.inl 2) (.inr .scratch)
      id false (.inr .clockCopy) (some (.inr .archiveCopy))
  | .inr .archiveCopy => Reduction.MachineTransfer.loopAt (.inr .archive) (.inr .scratch)
      id false (.inr .archiveCopy) (some (.inr .finalReverse))
  | .inr .finalReverse => Reduction.MachineTransfer.loopAt (.inr .scratch) (.inr .output)
      id false (.inr .finalReverse) none

def machine : FinTM2 where
  K := Tape
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .copyFirst
  σ := State
  initialState := initialState
  m := program

theorem clockStep (extra : ExtraTape → List Bool) (register : Option Bool)
    (a b : MachineLogCounter.machine.Cfg)
    (h : MachineLogCounter.machine.step a = some b) :
    TM2.step program (clockConfiguration extra register a) =
      some (clockConfiguration extra register b) := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => cases h
      | some label =>
          have hb := Option.some.inj h
          subst b
          exact congrArg some (clockStatement_simulation extra register
            (MachineLogCounter.program label) state tapes)

end MaxCutGames.Foundations.Complexity.GraphCounterModel

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

theorem initialMemory (word : List Bool) :
    initList machine word =
      ⟨some (.inr .copyFirst), initialState, startMemory word [] []⟩ := by
  have ht : (initList machine word).stk = startMemory word [] [] := by
    funext tape
    cases tape with
    | inl k => simp [initList, machine, startMemory]
    | inr k =>
      cases k <;> simp [initList, machine, startMemory, startExtra]
      rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

end MaxCutGames.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_GraphCounterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem finish_eq (word : List Bool) :
    (⟨none, initialState, frame [] [] [] [] word⟩ : TM2.Cfg Alphabet Label State) =
      haltList machine word := by
  unfold haltList
  congr 1
  funext tape
  cases tape with
  | inl i => simp [machine, frame]
  | inr k =>
    cases k <;> simp [machine, frame]
    rfl

end MaxCutGames.Foundations.Complexity.GraphCounterFinish

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

namespace MaxCutGames.Foundations.Complexity.MachineInitialHeaders

open Turing
open Reduction.MachineTransfer
open Reduction.MachineSubstitution
open MachineCopy

variable {K Λ σ : Type} [DecidableEq K]

theorem prefixTrace (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (atRestore : program restore = loopAt scratch source id false restore exit)
    (base : K → List Bool) (n : ℕ) (suffix : List Bool)
    (hsource : base source = encodeWord n ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 2]
      (some ⟨some again, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base output
        (List.replicate (scale * n) true ++ base output)⟩ := by
  have scan := prefixScanTrace source scratch output hst hso hto scale again restore
    program atScan base n suffix [] (base output) ambient register
  have hstart : forkTapes source scratch output base (encodeWord n ++ suffix) []
      (base output) = base := by
    rw [← hsource, ← scratchEmpty]
    exact forkTapes_self source scratch output base
  rw [hstart] at scan
  simp only [List.append_nil] at scan
  let emitted := List.replicate (scale * n) true ++ base output
  let scanned := forkTapes source scratch output base (false :: suffix)
    (List.replicate n true) emitted
  have restoreTrace := transferAt_fromTapes scratch source (Ne.symm hst) id false
    restore exit program atRestore scanned ambient none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restore, (ambient, none), scanned⟩) = _ at restoreTrace
  have hs : scanned scratch = List.replicate n true := by simp [scanned, hto]
  have hi : scanned source = false :: suffix := by simp [scanned, hst, hso]
  rw [hs, hi] at restoreTrace
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at restoreTrace
  have hrestored : tapesAt scratch source scanned []
      (List.replicate n true ++ false :: suffix) = Function.update base output emitted := by
    funext k
    by_cases hks : k = source
    · subst k
      simp [tapesAt, hso, hsource, encodeWord]
    · by_cases hkt : k = scratch
      · subst k
        simp [tapesAt, Ne.symm hst, hto, scratchEmpty]
      · by_cases hko : k = output
        · subst k
          simp [tapesAt, scanned, forkTapes, Ne.symm hso, Ne.symm hto]
        · simp [tapesAt, scanned, forkTapes, hks, hkt, hko]
  rw [hrestored] at restoreTrace
  rw [show 2 * n + 2 = (n + 1) + (n + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restoreTrace

def prefixInTime (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (atRestore : program restore = loopAt scratch source id false restore exit)
    (base : K → List Bool) (n : ℕ) (suffix : List Bool)
    (hsource : base source = encodeWord n ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base output
        (List.replicate (scale * n) true ++ base output)⟩) (2 * n + 2) where
  steps := 2 * n + 2
  evals_in_steps := prefixTrace source scratch output hst hso hto scale again restore exit
    program atScan atRestore base n suffix hsource scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

/-- The complete raw initial-graph header phase, in an arbitrary caller program.
Only the output tape changes; its old suffix is preserved verbatim. -/
theorem headerTrace (nTape mTape scratch output : K)
    (_hnm : nTape ≠ mTape) (hnt : nTape ≠ scratch) (hno : nTape ≠ output)
    (hmt : mTape ≠ scratch) (hmo : mTape ≠ output) (hto : scratch ≠ output)
    (scanN restoreN scanM1 restoreM1 closeFirst scanM6 restoreM6 closeSecond : Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScanN : program scanN = prefixScan nTape scratch output 1 scanN restoreN)
    (atRestoreN : program restoreN = loopAt scratch nTape id false restoreN (some scanM1))
    (atScanM1 : program scanM1 = prefixScan mTape scratch output 1 scanM1 restoreM1)
    (atRestoreM1 : program restoreM1 = loopAt scratch mTape id false restoreM1 (some closeFirst))
    (atCloseFirst : program closeFirst = pushWord output [true, false]
      (exitAt output (some scanM6)))
    (atScanM6 : program scanM6 = prefixScan mTape scratch output 6 scanM6 restoreM6)
    (atRestoreM6 : program restoreM6 = loopAt scratch mTape id false restoreM6 (some closeSecond))
    (atCloseSecond : program closeSecond = pushWord output [true, false] (exitAt output exit))
    (base : K → List Bool) (n m : ℕ) (nSuffix mSuffix : List Bool)
    (hn : base nTape = encodeWord n ++ nSuffix)
    (hm : base mTape = encodeWord m ++ mSuffix) (ht : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some scanN, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base output
        ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output)⟩ := by
  let out1 := List.replicate n true ++ base output
  let out2 := List.replicate m true ++ out1
  let out3 := [false, true] ++ out2
  let out4 := List.replicate (6 * m) true ++ out3
  let out5 := [false, true] ++ out4
  let b1 := Function.update base output out1
  let b2 := Function.update base output out2
  let b3 := Function.update base output out3
  let b4 := Function.update base output out4
  let b5 := Function.update base output out5
  have first := prefixTrace nTape scratch output hnt hno hto 1 scanN restoreN
    (some scanM1) program atScanN atRestoreN base n nSuffix hn ht ambient register
  simp only [Nat.one_mul] at first
  change (MachineComposition.advance (TM2.step program))^[2 * n + 2]
    (some ⟨some scanN, (ambient, register), base⟩) =
    some ⟨some scanM1, (ambient, none), b1⟩ at first
  have second := prefixTrace mTape scratch output hmt hmo hto 1 scanM1 restoreM1
    (some closeFirst) program atScanM1 atRestoreM1 b1 m mSuffix
    (by simp [b1, hmo, hm]) (by simp [b1, hto, ht]) ambient none
  simp only [Nat.one_mul, b1, Function.update_self, Function.update_idem] at second
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM1, (ambient, none), b1⟩) =
    some ⟨some closeFirst, (ambient, none), b2⟩ at second
  have third := literalTrace output [true, false] closeFirst (some scanM6)
    program atCloseFirst b2 ambient none
  simp only [b2, Function.update_self, Function.update_idem] at third
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeFirst, (ambient, none), b2⟩) =
    some ⟨some scanM6, (ambient, none), b3⟩ at third
  have fourth := prefixTrace mTape scratch output hmt hmo hto 6 scanM6 restoreM6
    (some closeSecond) program atScanM6 atRestoreM6 b3 m mSuffix
    (by simp [b3, hmo, hm]) (by simp [b3, hto, ht]) ambient none
  simp only [b3, Function.update_self, Function.update_idem] at fourth
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM6, (ambient, none), b3⟩) =
    some ⟨some closeSecond, (ambient, none), b4⟩ at fourth
  have fifth := literalTrace output [true, false] closeSecond exit
    program atCloseSecond b4 ambient none
  simp only [b4, Function.update_self, Function.update_idem] at fifth
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeSecond, (ambient, none), b4⟩) =
    some ⟨exit, (ambient, none), b5⟩ at fifth
  have total := trace_trans_inline_MachineInitialHeaders _ (trace_trans_inline_MachineInitialHeaders _ (trace_trans_inline_MachineInitialHeaders _ (trace_trans_inline_MachineInitialHeaders _ first second)
    third) fourth) fifth
  have hsteps : (((2 * n + 2) + (2 * m + 2)) + 1 + (2 * m + 2)) + 1 =
      2 * n + 4 * m + 8 := by omega
  rw [hsteps] at total
  have hout : out5 = (encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output := by
    simp only [out5, out4, out3, out2, out1, encodeWords, encodeWord,
      List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
      List.append_nil, List.nil_append, List.append_assoc, List.singleton_append]
    rw [show n + m + 1 = 1 + m + n by omega,
      show 6 * m + 1 = 1 + 6 * m by omega]
    simp only [List.replicate_add, List.replicate_one, List.cons_append,
      List.nil_append, List.append_assoc]
  simpa only [b5, hout] using total

end MaxCutGames.Foundations.Complexity.MachineInitialHeaders

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionEmission
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

theorem header_template (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      headerBits n q Q := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    headerTokens, newHeaderField, MachineSubdivisionInit.resultTapes,
    headerBits, encodeWords]

theorem header_result (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.outputTapes (MachineSubdivisionInit.resultTapes n q Q body)
      .accumulator (headerBits n q Q) = resultTapes n q Q body := by
  simp only [MachineFieldTemplate.outputTapes, MachineSubdivisionInit.resultTapes,
    List.append_nil, resultTapes]

end MaxCutGames.Explicit.MachineSubdivisionEmission

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionTableRead
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

namespace MaxCutGames.Explicit.MachineSubdivisionBody

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def tableBits {q : Nat} (table : Target.PermutationTable q) : List Bool :=
  encodeWords (tableWords table)

structure Ready {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Prop where
  input : base .input = encodeWord u ++ encodeWord v ++ tableBits table ++ suffix
  uEmpty : base .u = []
  vEmpty : base .v = []
  permutationEmpty : base .permutation = []
  reverseEmpty : base .permutationReverse = []
  scratchEmpty : base .copyScratch = []

def afterU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .u base u (encodeWord v ++ tableBits table ++ suffix)

def afterV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .v (afterU base u v table suffix) v (tableBits table ++ suffix)

def afterTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineSubdivisionTableRead.finalTapes (afterV base u v table suffix) suffix (tableBits table)

def rowPayload {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : List Bool :=
  MachineFieldTemplate.templateOutput (rowTokens q)
    (fun j => afterTable base u v table suffix (rowField j))

def afterRows {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterTable base u v table suffix) .accumulator
    (rowPayload base u v table suffix)

def afterDrainU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterRows base u v table suffix) .u []

def afterDrainV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainU base u v table suffix) .v []

def afterDrainTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainV base u v table suffix) .permutation []

def bodyResult {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  incrementTapes (afterDrainTable base u v table suffix)

def bodyBudget {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Nat :=
  (u + 2) + (v + 2) + (2 * (q * (q + 1)) + 2) +
    (3 * MachineFieldTemplate.copiedLength (rowTokens q)
      (fun j => afterTable base u v table suffix (rowField j)) + 37) +
    ((afterRows base u v table suffix .u).length + 1) +
    ((afterDrainU base u v table suffix .v).length + 1) +
    ((afterDrainV base u v table suffix .permutation).length + 1) + 1

end MaxCutGames.Explicit.MachineSubdivisionBody

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

namespace MaxCutGames.Explicit.MachineSubdivisionLoopFrame

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def bodyBits {n q : Nat} (edges : List (Constraint n q)) : List Bool :=
  encodeWords (edges.flatMap constraintWords)

@[simp] theorem bodyBits_nil {n q : Nat} : bodyBits ([] : List (Constraint n q)) = [] := rfl

theorem bodyBits_cons {n q : Nat} (edge : Constraint n q) (edges : List (Constraint n q)) :
    bodyBits (edge :: edges) =
      encodeWord edge.source.val ++ encodeWord edge.target.val ++
        MachineSubdivisionBody.tableBits edge.permutation ++ bodyBits edges := by
  simp [bodyBits, constraintWords, encodeWords, MachineSubdivisionBody.tableBits,
    List.append_assoc]

def rowBits {n q : Nat} (Q e : Nat) (edge : Constraint n q) : List Bool :=
  encodeWords [edge.source.val, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e + 1] ++ identityBits q ++
  encodeWords [edge.target.val, n + Q + 2 * e + 1] ++
    MachineSubdivisionBody.tableBits edge.permutation

def outputRows {n q : Nat} (Q : Nat) : Nat → List (Constraint n q) → List Bool
  | _, [] => []
  | e, edge :: edges => rowBits Q e edge ++ outputRows Q (e + 1) edges

def frame {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => bodyBits edges
  | .remaining => encodeWord edges.length
  | .middle => encodeWord (n + e)
  | .first => encodeWord (n + Q + 2 * e)
  | .last => encodeWord (n + Q + 2 * e + 1)
  | .accumulator => emitted.reverse
  | _ => MachineSubdivisionInit.resultTapes n q Q [] tape

def afterGuard {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) : Tape → List Bool :=
  Function.update (frame Q e (edge :: edges) emitted) .remaining (encodeWord edges.length)

theorem frame_prepared {n q : Nat} (edges : List (Constraint n q)) :
    frame edges.length 0 edges (MachineSubdivisionEmission.headerBits n q edges.length) =
      MachineSubdivisionEmission.resultTapes n q edges.length (bodyBits edges) := by
  funext tape
  cases tape <;> simp [frame, MachineSubdivisionEmission.resultTapes,
    MachineSubdivisionInit.resultTapes]

theorem ready {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.Ready (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) := by
  constructor
  · simpa only [afterGuard, Function.update_of_ne (by decide : Tape.input ≠ .remaining),
      frame] using bodyBits_cons edge edges
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]

end MaxCutGames.Explicit.MachineSubdivisionLoopFrame

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

namespace MaxCutGames.Explicit.MachineSubdivisionBodySpec

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction
open MachineSubdivisionProgram MachineSubdivisionBody

def resultTapes {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .u | .v | .permutation | .permutationReverse => []
  | .middle => true :: base .middle
  | .first => true :: true :: base .first
  | .last => true :: true :: base .last
  | .accumulator => (rowPayload base u v table suffix).reverse ++ base .accumulator
  | k => base k

/-- Every tape at the body boundary, including all preserved headers and counters. -/
theorem bodyResult_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (_ready : Ready base u v table suffix) :
    bodyResult base u v table suffix = resultTapes base u v table suffix := by
  funext k
  cases k <;> simp [bodyResult, incrementTapes, afterDrainTable, afterDrainV,
    afterDrainU, afterRows, MachineFieldTemplate.outputTapes, afterTable,
    MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, resultTapes]

theorem result_input {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .input = suffix := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem result_accumulator {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .accumulator =
      (rowPayload base u v table suffix).reverse ++ base .accumulator := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem encodeWord_succ (n : Nat) : encodeWord (n + 1) = true :: encodeWord n := by
  simp [encodeWord, List.replicate_succ]

theorem result_indices {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyResult base u v table suffix .middle = encodeWord (n + (e + 1)) ∧
    bodyResult base u v table suffix .first = encodeWord (n + Q + 2 * (e + 1)) ∧
    bodyResult base u v table suffix .last = encodeWord (n + Q + 2 * (e + 1) + 1) := by
  rw [bodyResult_eq base u v table suffix ready]
  have hm : n + (e + 1) = (n + e) + 1 := by omega
  have hf : n + Q + 2 * (e + 1) = (n + Q + 2 * e) + 1 + 1 := by omega
  have hl : n + Q + 2 * (e + 1) + 1 = (n + Q + 2 * e + 1) + 1 + 1 := by omega
  simp [resultTapes, middle, first, last, hm, hf, encodeWord_succ]

/-- Four whole rows, with the final table already in left-to-right orientation. -/
def rowBits {q : Nat} (u middle first last v : Nat) (table : Target.PermutationTable q) :
    List Bool :=
  encodeWords
    ([u, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, last] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [v, last] ++ tableWords table)

theorem rowPayload_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (middle first last : Nat)
    (hm : base .middle = encodeWord middle) (hf : base .first = encodeWord first)
    (hl : base .last = encodeWord last) :
    rowPayload base u v table suffix = rowBits u middle first last v table := by
  simp [rowPayload, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput, rowField,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, hm, hf, hl,
    rowBits, tableBits, encodeWords, List.append_assoc]

/-- The natural-word description is literally the established finite-target
constraint codec, rather than an alternative encoding. -/
theorem rowBits_eq_dynamic {N q : Nat} (vertices : Fin 5 → Fin N)
    (table : Target.PermutationTable q) :
    rowBits (vertices 0).val (vertices 2).val (vertices 1).val (vertices 3).val
      (vertices 4).val table = MachineSubdivisionDynamicRows.rowBits vertices table := by
  simp [rowBits, MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionDynamicRows.rows,
    constraintWords, List.append_assoc]

/-- One conservative bound uniform over all occurrences in this output.
Only the fixed alphabet and the runtime header sizes appear in the polynomial. -/
theorem bodyBudget_le {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (hu : u < n) (hv : v < n) (he : e ≤ Q)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyBudget base u v table suffix ≤ 100 * (n + 3 * Q + q * (q + 1) + 1) := by
  have ht : (tableBits table).length ≤ q * (q + 1) :=
    GameEncodingSize.tableBits_length_le table
  simp [bodyBudget, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.copiedLength, rowField,
    afterDrainV, afterDrainU, afterRows, MachineFieldTemplate.outputTapes,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, middle, first, last] at *
  omega

end MaxCutGames.Explicit.MachineSubdivisionBodySpec

/-! Complete physical occurrence traversal of the subdivision program. -/

namespace MaxCutGames.Explicit.MachineSubdivisionLoop

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame

theorem rowPayload_eq {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.rowPayload (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) = rowBits Q e edge := by
  rw [MachineSubdivisionBodySpec.rowPayload_eq _ _ _ _ _ (ready Q e edge edges emitted)
    (n + e) (n + Q + 2 * e) (n + Q + 2 * e + 1) rfl rfl rfl]
  simp only [MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem bodyResult_eq_frame {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.bodyResult (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) =
      frame Q (e + 1) edges (emitted ++ rowBits Q e edge) := by
  have indices := MachineSubdivisionBodySpec.result_indices
    (afterGuard Q e edge edges emitted) edge.source.val edge.target.val edge.permutation
    (bodyBits edges) (ready Q e edge edges emitted) n Q e rfl rfl rfl
  funext tape
  cases tape with
  | middle => exact indices.1
  | first => exact indices.2.1
  | last => exact indices.2.2
  | input => exact MachineSubdivisionBodySpec.result_input _ _ _ _ _ (ready Q e edge edges emitted)
  | accumulator =>
    rw [MachineSubdivisionBodySpec.result_accumulator _ _ _ _ _ (ready Q e edge edges emitted),
      rowPayload_eq]
    simp [afterGuard, frame, List.reverse_append]
  | _ =>
    rw [MachineSubdivisionBodySpec.bodyResult_eq _ _ _ _ _ (ready Q e edge edges emitted)]
    simp [MachineSubdivisionBodySpec.resultTapes, afterGuard, frame,
      MachineSubdivisionInit.resultTapes]

end MaxCutGames.Explicit.MachineSubdivisionLoop

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace MaxCutGames.Foundations.PCP.RoundTables

abbrev BaseTable := PreprocessingTables.BaseTable

end MaxCutGames.Foundations.PCP.RoundTables

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineCleanup
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

/-- Read fixed register slots from the actual unary 0/1 word encoding. Each
slot consumes one symbol for false and two symbols for true. -/
def readUnarySlots (source : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop source (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop source (fun state _ => state) (readUnarySlots source slots next))
          (readUnarySlots source slots next))

end RelationReader

/-- Merely rearranges finite registers to match the affine-emitter state.
No tape content or unbounded integer is moved into the internal state. -/
def readerStateEquiv (σ : Type) (N : Nat) :
    (((σ × Unit) × Option Bool) × Buffer N) ≃ (((σ × Buffer N) × Unit) × Option Bool) where
  toFun state := (((state.1.1.1, state.2), state.1.1.2), state.1.2)
  invFun state := (((state.1.1.1, state.1.2), state.2), state.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

section AmbientRelation

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := ((σ × Buffer 4096) × Unit) × Option Bool

def readRelationAt (source : K) (exit : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit))

end AmbientRelation

namespace Program

open PCP.AlphabetTable

def guard {hc rc : Nat} (again finish : Label hc rc) :
    TM2.Stmt (fun _ : Tape => Bool) (Label hc rc) (State Unit) :=
  .peek .input (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => (state.1, none)) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => finish)))

end Program

end MaxCutGames.Foundations.Complexity.FinalCNFMachine

end OAI
end


