-- Prove2me | Definitions.Def_OAIQ069A004
-- name    : OAIQ069A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:49:02.751993+00:00
-- url     : https://prove2.me/theorems/91679db1-e8a7-40b2-b76a-23f9a82706c3
-- title:
--   Definitions bundle OAIQ069A004 of the split of OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 721 declarations of OpenAI's Lean: 387 definitions, 6 inductive types or structures, 10 instances and 318 theorems. The definitions and types are `OAI.IndependentSetsGames.Foundations.Complexity.MachineFixedBlockMap.emptyBuffer`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineInitialHeaders.prefixInTime`, `OAI.IndependentSetsGames.Foundations.Complexity.MachinePaddingBounds.inputSize`, `OAI.IndependentSetsGames.Foundations.Complexity.MachinePreservingLookupClean.steps`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRegularDummyRow.Input`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRegularDummyRow.memory`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow.CoreState`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow.coreInitialState`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow.coreRotorStateEquiv`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalBody.CoreState`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRegularOwnerBody.CoreState`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineRepeat.executeSequence`, `OAI.IndependentSetsGames.Foundations.Complexity.MachineUnaryEqualityBit.bitEncoding`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringGlobalEnumeration.enumeration`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringGlobalEnumeration.extraTapeEquiv`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringGlobalEnumeration.globalTapeEquiv`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringGlobalEnumeration.headerTapeEquiv`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringGlobalEnumeration.sharedTapeEquiv`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineEqualityField.Tape`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineField.Tape`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineFinish.afterD`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineFinish.afterHeaders`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineFinish.steps`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal.Tape`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal.enumeration`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal.headerDarts`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal.headerVertices`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal.inputTape`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal.outputTape`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal.placement`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineInitialize.finalOutput`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineInitialize.initialGlobalTapes`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop.HeaderAlphabet`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop.finalConfiguration`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop.headerProgram`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop.initialTapes`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop.scanConfiguration`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineOuterLoop.Placement`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineOuterLoop.counter`, `OAI.IndependentSetsGames.Foundations.Complexity.PoweringMachineRelationField.lookupTapes` and 353 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `IndependentSets_Encoding_BinaryNameTables`, `IndependentSets_Encoding_BinarySyntax`, `IndependentSets_Encoding_Completion`, `IndependentSets_Encoding_GeometryExpr`, `IndependentSets_Encoding_Target`, `IndependentSets_Encoding_TargetLCExpr`, `IndependentSets_Expansion_Capped`, `IndependentSets_Expansion_CayleySpectral`, `IndependentSets_Expansion_CayleyTailCount`, `IndependentSets_Expansion_ExpanderFamily`, `IndependentSets_Expansion_ExpanderRowControl`, `IndependentSets_Expansion_ExpanderTableEnumeration`, `IndependentSets_Expansion_ExpanderTables`, `IndependentSets_Expansion_Expanders`, `IndependentSets_Expansion_GraphRounding`, `IndependentSets_Expansion_Indicators`, `IndependentSets_Expansion_PoweringLabels`, `IndependentSets_Expansion_PoweringTableLayout`, `IndependentSets_Expansion_PoweringWalks`, `IndependentSets_Expansion_PreprocessingPaddingWords`, `IndependentSets_Expansion_PreprocessingRegularWords`, `IndependentSets_Expansion_SpectralReturn`, `IndependentSets_Expansion_Supported2`, `IndependentSets_Fourier_Contexts`, `IndependentSets_Fourier_Decoder`, `IndependentSets_Fourier_Folding`, `IndependentSets_Fourier_Game`, `IndependentSets_Fourier_Gap`, `IndependentSets_Fourier_Walsh`, `IndependentSets_Fourier_Walsh2`, `IndependentSets_Geometry_GeometryAntipodes`, `IndependentSets_Geometry_GeometryDistance`, `IndependentSets_Geometry_GeometryInitialize`, `IndependentSets_Geometry_GeometryLink`, `IndependentSets_Geometry_GeometryLocations`, `IndependentSets_Geometry_GeometryNaming`, `IndependentSets_Geometry_GeometryOutput`, `IndependentSets_Machines_Initialization`, `IndependentSets_Machines_Machine`, `IndependentSets_Machines_MachineControl`, `IndependentSets_Machines_MachineFixedBlockMap`, `IndependentSets_Machines_MachineInitialHeaders`, `IndependentSets_Machines_MachineLazyTableRuntime`, `IndependentSets_Machines_MachinePaddingBounds`, `IndependentSets_Machines_MachinePreservingLookupClean`, `IndependentSets_Machines_MachineRegularDummyRow`, `IndependentSets_Machines_MachineRegularMetadata`, `IndependentSets_Machines_MachineRegularOriginalBody`, `IndependentSets_Machines_MachineRegularOriginalRow`, `IndependentSets_Machines_MachineRegularOwnerProgram`, `IndependentSets_Machines_MachineRegularVertexBlock`, `IndependentSets_Machines_MachineRepeat`, `IndependentSets_Machines_MachineUnaryCounter`, `IndependentSets_Machines_MachineUnaryEqualityBit`, `IndependentSets_Machines_MachineUnaryLess`, `IndependentSets_Machines_OldSelectSteps`, `IndependentSets_Machines_PCPGapMachine`, `IndependentSets_Machines_PoweringGlobalEnumeration`, `IndependentSets_Machines_PoweringMachineEqualityField`, `IndependentSets_Machines_PoweringMachineField`, `IndependentSets_Machines_PoweringMachineFinish`, `IndependentSets_Machines_PoweringMachineGlobal`, `IndependentSets_Machines_PoweringMachineInitialize`, `IndependentSets_Machines_PoweringMachineLoop`, `IndependentSets_Machines_PoweringMachineOuterLoop`, `IndependentSets_Machines_PoweringMachineRelationField`, `IndependentSets_Machines_PoweringMachineRow`, `IndependentSets_Machines_PoweringMachineRowBody`, `IndependentSets_Machines_PoweringMachineRowHeaders`, `IndependentSets_Machines_PoweringMachineTapes`, `IndependentSets_Machines_PoweringMachineVertex`, `IndependentSets_Machines_PoweringMachineWord`, `IndependentSets_Machines_RawInitialMachineBudget`, `IndependentSets_Machines_RawInitialMachineFinish`, `IndependentSets_Machines_RawInitialMachineLoopData`, `IndependentSets_Machines_RawInitialMachineRows`, `IndependentSets_Machines_RawInitialMachineStart`, `IndependentSets_Machines_SelectAlphabet`, `IndependentSets_Machines_VertexLabel`, `IndependentSets_PCP_Addresses`, `IndependentSets_PCP_AlphabetGraph`, `IndependentSets_PCP_AlphabetGraphBounds`, `IndependentSets_PCP_AlphabetReduction`, `IndependentSets_PCP_Ambient`, `IndependentSets_PCP_AmplificationIteration`, `IndependentSets_PCP_AmplificationRound`, `IndependentSets_PCP_AssignmentTester`, `IndependentSets_PCP_BoundedIteration`, `IndependentSets_PCP_ClauseVerifier`, `IndependentSets_PCP_Cleanup`, `IndependentSets_PCP_CodeComposition`, `IndependentSets_PCP_CompareLoop`, `IndependentSets_PCP_ConstraintGraph`, `IndependentSets_PCP_Driver`, `IndependentSets_PCP_EmitRows`, `IndependentSets_PCP_Emitter`, `IndependentSets_PCP_Enumeration`, `IndependentSets_PCP_FinalBooleanVerifier`, `IndependentSets_PCP_Gap`, `IndependentSets_PCP_GenericGraphTables`, `IndependentSets_PCP_GeometryPointTable`, `IndependentSets_PCP_GraphTables`, `IndependentSets_PCP_InitialGraph`, `IndependentSets_PCP_LCTable`, `IndependentSets_PCP_LabelCoverData`, `IndependentSets_PCP_Minimum`, `IndependentSets_PCP_NameCompaction`, `IndependentSets_PCP_PCPIteration`, `IndependentSets_PCP_QueryIncidence`, `IndependentSets_PCP_RawInitialTables`, `IndependentSets_PCP_ReadRelation`, `IndependentSets_PCP_RoundGap`, `IndependentSets_PCP_Semantics2`, `IndependentSets_PCP_Setup`, `IndependentSets_PCP_VerifierCNF`, `IndependentSets_Reduction_FiniteScan`, `IndependentSets_Reduction_FloydLoop`, `IndependentSets_Reduction_FrameNonempty`, `IndependentSets_Reduction_SamplerParameters`, `IndependentSets_Reduction_Simple`, `IndependentSets_Reduction_StoredFloyd`, `IndependentSets_Reduction_TargetRead`, `IndependentSets_Repetition_ActualGame`, `IndependentSets_Repetition_Basic`, `IndependentSets_Repetition_Conditionals`, `IndependentSets_Repetition_CoordinateCompletion`, `IndependentSets_Repetition_DistributionIdentities`, `IndependentSets_Repetition_KernelSampling`, `IndependentSets_Repetition_MaskedVariation`, `IndependentSets_Repetition_Mixture`, `IndependentSets_Repetition_PartialReveal`, `IndependentSets_Repetition_ProfileBounds`, `IndependentSets_Repetition_QuestionMarginal`, `IndependentSets_Repetition_Rectangle`, `IndependentSets_Repetition_Rectangle2`, `IndependentSets_Repetition_Reveal`, `IndependentSets_Repetition_RevealFactorization`, `IndependentSets_Repetition_Sampling`, `IndependentSets_Repetition_SelectedCompletionGame`, `IndependentSets_Repetition_SelectedInformation`, `IndependentSets_Repetition_SelectedJoint`, `IndependentSets_Repetition_SelectedMarginal`, `IndependentSets_Repetition_SelectedProfileBudget`, `IndependentSets_Repetition_SelectedProfiles`, `IndependentSets_Repetition_SharedSampling`, `IndependentSets_Repetition_TotalVariation`, `IndependentSets_Repetition_TraceLaw`, `IndependentSets_Repetition_Value`.
--
--   **Imports.** It imports the published bundle `Def_IndependentSets`; the bundles `OAIQ069A000`, `OAIQ069A001` and `OAIQ069A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ069A006` and `OAIQ069A007`; the statements `OAI.LargeIndependentSets.LCInput.uniform_repetition` and `OAI.LargeIndependentSets.finite_source_soundness`; the proof of `OAI.LargeIndependentSets.LCInput.uniform_repetition`.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 1581d4c

import Mathlib
import Definitions.Def_IndependentSets
import Definitions.Def_OAIQ069A000
import Definitions.Def_OAIQ069A001
import Definitions.Def_OAIQ069A002

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_Target
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Target

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.«variables» → Bool,
    ∀ clause ∈ formula.clauses, clause.eval assignment = true

end IndependentSetsGames.Foundations.Target

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRepeat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRepeat
open Turing

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseTrace (count : Nat) (word counter : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[count+1]
      (some (inputConfig M .parse ((encodeWord count).map input.symm ++ word) counter)) =
    some (inputConfig M .guard word (List.replicate count (input.symm true) ++ counter)) := by
  induction count generalizing counter with
  | zero =>
    simp only [encodeWord, List.replicate_zero, List.nil_append, List.map_singleton,
      List.singleton_append, Nat.zero_add, Function.iterate_one]
    exact parseStep_false M input output word counter
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[count+1]
      ((machine M input output).step
        (inputConfig M .parse ((encodeWord (count+1)).map input.symm ++ word) counter)) = _
    simp only [encodeWord, List.replicate_succ, List.cons_append, List.map_cons,
      List.map_append, List.map_replicate, List.map_nil, List.append_assoc, List.nil_append]
    rw [parseStep_true]
    have h := ih (input.symm true :: counter)
    have hc : List.replicate count (input.symm true) ++ input.symm true :: counter =
        input.symm true :: (List.replicate count (input.symm true) ++ counter) := by
      rw [← List.singleton_append, ← List.append_assoc,
        ← List.replicate_succ', List.replicate_succ, List.cons_append]
    rw [hc] at h
    simp only [encodeWord, List.map_append, List.map_replicate, List.map_singleton,
      List.singleton_append, List.append_assoc] at h
    exact h

def executeSequence (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + loopBudget count words budgets) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])
      (some (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))) (count+1) := {
    steps := count+1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[count+1]
        (some (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])) = _
      have parsedTrace := parseTrace M input output count
        ((words 0).map input.symm) []
      simp only [List.append_nil] at parsedTrace
      exact parsedTrace
    steps_le_m := le_refl _
  }
  have body := loopExecution M input output count words budgets runs
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed body
  rw [inputConfig_init M input output] at full
  simp only [TM2OutputsInTime, Option.map_some]
  erw [List.map_append]
  rw [Nat.add_comm (loopBudget count words budgets)] at full
  exact full

end IndependentSetsGames.Foundations.Complexity.MachineRepeat

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Cleanup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

@[simp] theorem clearTapes_selected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (i : Fin n) : clearTapes selected base (selected i) = [] := by
  rw [clearTapes_apply, ite_eq_left ⟨i, rfl⟩]

theorem clearTapes_unselected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (k : K) (notSelected : ∀ i, selected i ≠ k) :
    clearTapes selected base k = base k := by
  rw [clearTapes_apply]
  simp [notSelected]

theorem cleanupTrace {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[actualCost selected base]
      (some ⟨some (labels 0), (ambient, register), base⟩) =
      some ⟨exit, (initial, none), clearTapes selected base⟩ := by
  induction n generalizing base ambient register with
  | zero =>
      change some (TM2.stepAux (program (labels 0)) (ambient, register) base) = _
      rw [show program (labels 0) = finish initial exit from atFinish]
      cases exit <;> rfl
  | succ n ih =>
      rw [actualCost, Function.iterate_add_apply]
      have first := MachineDrain.drainTrace (selected 0) (labels (0 : Fin (n + 1)).castSucc)
        (some (labels (0 : Fin (n + 1)).succ)) program (atDrain 0)
        base (base (selected 0)) ambient register
      simp only [Function.update_eq_self, Fin.castSucc_zero] at first
      rw [first]
      exact ih (fun i : Fin n => selected i.succ) (fun i => labels i.succ)
        (fun i => atDrain i.succ) atFinish (Function.update base (selected 0) []) ambient none

def cleanupInTime {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register), base⟩
      (some ⟨exit, (initial, none), clearTapes selected base⟩)
      ((∑ i, (base (selected i)).length) + n + 1) where
  steps := actualCost selected base
  evals_in_steps := cleanupTrace selected labels initial exit program atDrain atFinish
    base ambient register
  steps_le_m := actualCost_le selected base

theorem clearTapes_outputOnly {n : Nat} (selected : Fin n → K)
    (output : K) (base : K → List Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    clearTapes selected base = fun k => if k = output then base output else [] := by
  funext k
  by_cases h : k = output
  · subst k
    simp [clearTapes_unselected selected base output excludesOutput]
  · rw [clearTapes_apply]
    simp [h, coversOther k h]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Cleanup

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringWalks
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

end IndependentSetsGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringLabels
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

end IndependentSetsGames.Foundations.PCP.PoweringLabels

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ConstraintGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

end ConstraintGraph

end IndependentSetsGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GenericGraphTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GenericGraphTables

open IndependentSetsGames.Foundations.Complexity

variable {q : Nat}

instance instDecidableValid {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

theorem vertices_le_tableBits_length (table : (Table q)) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end IndependentSetsGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineControl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open IndependentSetsGames.Foundations.Complexity

instance instFintypeTape : Fintype Tape where
  elems := {.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan,
    .compareLeft, .compareRight, .reversed, .output}
  complete tape := by cases tape <;> simp

theorem setupPorts_injective : Function.Injective setupPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [setupPorts]

def headPorts : Fin 6 → Tape :=
  ![.original, .reverseIndex, .scan, .indexScan, .head, .scratch]

theorem headPorts_injective : Function.Injective headPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headPorts]

theorem cleanupPorts_ne_output (i : Fin 15) : cleanupPorts i ≠ .output := by
  fin_cases i <;> simp [cleanupPorts]

theorem cleanupPorts_cover (tape : Tape) (h : tape ≠ .output) :
    ∃ i, cleanupPorts i = tape := by
  cases tape
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact (h rfl).elim

variable {Λ : Type} {q : Nat}

def transportInTime {K τ υ : Type} [DecidableEq K] {Γ : K → Type}
    (e : τ ≃ υ) (p : Λ → TM2.Stmt Γ Λ τ)
    {start finish : TM2.Cfg Γ Λ τ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step p) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step (MachineControl.program (Equiv.refl Λ) e p))
      (MachineControl.configuration id e start)
      (some (MachineControl.configuration id e finish)) budget := by
  apply MachineComposition.liftExecutionInTime _ _ (MachineControl.configuration id e) _ run
  intro a b hab
  have h := MachineControl.step_simulation (Equiv.refl Λ) e p a
  rw [hab] at h
  exact h

end IndependentSetsGames.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ClauseVerifier
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.clauseAnswerFintype _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP

open Target

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

theorem honest_satisfies {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) :
    localSatisfies clause (honestAnswer clause assignment) = clause.eval assignment := rfl

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

def matchingSlots (a b : ClauseAnswer) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

def acceptedSlots {n : Nat} (clause : Clause n) (alice bob : ClauseAnswer) : Nat :=
  if localSatisfies clause alice then matchingSlots alice bob else 0

def clauseFailure {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Nat :=
  if clause.eval assignment then 0 else 1

abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.«variables» → Bool

def accepts (formula : Formula) (alice : AliceStrategy formula) (bob : BobStrategy formula)
    (event : RandomEvent formula) : Bool :=
  localSatisfies (clauseAt formula event.1) (alice event.1) &&
    decide (answerAt (alice event.1) event.2 = bob (nameAt (clauseAt formula event.1) event.2))

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

def allIndices (formula : Formula) : List (Fin formula.clauses.length) :=
  List.finRange formula.clauses.length

end IndependentSetsGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Walsh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Hastad

open scoped BigOperators
open Finset

theorem bitSign_xor (b c : Bool) :
    bitSign (b ^^ c) = bitSign b * bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

theorem walsh_inversion {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (x : Cube I) :
    (∑ s, coefficient f s * walsh s x) = f x := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : Cube I) :
      (∑ s, (f y * walsh s y) * walsh s x) =
        f y * (if y = x then (Fintype.card (Cube I) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [walsh_symm (x := y), walsh_symm (x := x)]
    exact walsh_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

theorem walsh_inner {I : Type*} [Fintype I] [DecidableEq I] (f g : Cube I → ℝ) :
    (∑ s, coefficient f s * coefficient g s) = 𝔼 x, f x * g x := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  have h : (∑ s, (𝔼 y, f y * walsh s y) * (g x * walsh s x)) =
      g x * (∑ s, coefficient f s * walsh s x) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h, walsh_inversion]
  ring

theorem walsh_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) :
    (∑ s, coefficient f s ^ 2) = 𝔼 x, f x ^ 2 := by
  simpa [pow_two] using walsh_inner f f

end IndependentSetsGames.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Folding
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

end IndependentSetsGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Decoder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem sign_power_parity (b : Bool) (n : Nat) :
    bitSign b ^ n = bitSign (decide (Odd n) && b) := by
  cases b
  · simp [bitSign]
  · simp only [Bool.and_true, bitSign, ite_true, decide_eq_true_eq]
    rw [neg_one_pow_eq_ite]
    by_cases h : Even n
    · simp [h, Nat.not_odd_iff_even.mpr h]
    · simp [h, Nat.not_even_iff_odd.mp h]

end IndependentSetsGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AssignmentTester
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AssignmentTester

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def parity (s f : Cube A) : Bool :=
  decide (Odd ((Finset.univ.filter fun a => s a && f a = true).card))

theorem bitSign_parity (s f : Cube A) : bitSign (parity s f) = walsh s f := by
  have hw : walsh s f = (-1 : ℝ) ^
      (Finset.univ.filter fun a => s a && f a = true).card := by
    simp [walsh, bitSign, Finset.prod_ite]
  rw [hw]
  simpa [parity, bitSign] using
    (sign_power_parity true (Finset.univ.filter fun a => s a && f a = true).card).symm

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSign] <;> linarith

theorem parity_xor (s f g : Cube A) :
    parity s (cubeXor f g) = (parity s f ^^ parity s g) := by
  apply bitSign_injective
  rw [bitSign_parity, bitSign_xor, bitSign_parity, bitSign_parity, walsh_xor]

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

def singleMask (i : A) : Cube A := fun j => decide (j = i)

omit [Fintype A] in
theorem flipAt_eq_xor (i : A) (f : Cube A) : flipAt i f = cubeXor f (singleMask i) := by
  funext j
  by_cases h : j = i <;> simp [flipAt, cubeXor, singleMask, h]

theorem walsh_singleMask (s : Cube A) (i : A) :
    walsh s (singleMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [singleMask]
  · intro j _ hj
    simp [singleMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem parity_singleMask (s : Cube A) (i : A) : parity s (singleMask i) = s i := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_singleMask]

theorem parity_flipAt (s : Cube A) (i : A) (f : Cube A) (hs : s i = true) :
    parity s (flipAt i f) = !(parity s f) := by
  rw [flipAt_eq_xor, parity_xor, parity_singleMask, hs]
  cases parity s f <;> rfl

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

end IndependentSetsGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CodeComposition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

end IndependentSetsGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetReduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AlphabetReduction

open IndependentSetsGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

end IndependentSetsGames.Foundations.PCP.AlphabetReduction
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_QueryIncidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

def response (T : Verifier E X q) (assignment : X → Bool) (event : E) : Label q :=
  fun i => assignment (T.query event i)

def honestLabeling (T : Verifier E X q) (assignment : X → Bool) : Vertex E X → Label q
  | .inl event => response T assignment event
  | .inr address => encodeRight (assignment address)

def decodedAssignment (positive : 0 < q) (labeling : Vertex E X → Label q) : X → Bool :=
  fun address => decodeRight positive (labeling (.inr address))

def rejectedEvents [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Finset E :=
  Finset.univ.filter (fun event => T.accepts event (response T assignment event) = false)

def verifierRejectionCount [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Nat :=
  (rejectedEvents T assignment).card

end IndependentSetsGames.Foundations.PCP.QueryIncidence

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AlphabetGraph

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeOracle (G : ConstraintGraph V E A) (assignment : Address V E A → Bool) (e : E) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) → Bool :=
  fun tape => assignment (.inr (e, extendTape G e tape))

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

end IndependentSetsGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Enumeration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Enumeration

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators

theorem dartEquiv_reverse_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q (QueryIncidence.reverse ((event, slot), orientation))).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue (!orientation) :=
  dartEquiv_val m q event slot (!orientation)

theorem ordered_trans_finCongr {A : Type*} {a b : Nat}
    (order : A ≃ Fin a) (sameCount : a = b) :
    ordered (order.trans (finCongr sameCount)) = ordered order := by
  cases sameCount
  rfl

theorem ordered_product {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) :
    ordered (productEquiv left right) =
      (ordered left).flatMap (fun x => (ordered right).map (fun y => (x, y))) := by
  have atIndex (i : Fin a) (j : Fin b) (h : i.val * b + j.val < a * b) :
      (productEquiv left right).symm ⟨i.val * b + j.val, h⟩ =
        (left.symm i, right.symm j) := by
    have same : (⟨i.val * b + j.val, h⟩ : Fin (a * b)) = finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [same]
    simp [productEquiv]
  unfold ordered
  rw [List.ofFn_mul]
  simp only [atIndex, List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem ordered_event (m q : Nat) :
    ordered (eventEquiv m q) =
      (List.finRange m).flatMap (fun edge => (localEvents q).map (fun event => (edge, event))) := by
  change ordered (productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)) = _
  rw [ordered_product, ordered_refl]
  rfl

theorem ordered_dart (m q : Nat) :
    ordered (dartEquiv m q) =
      (List.finRange m).flatMap (fun edge =>
        (localEvents q).flatMap (fun event =>
          (List.finRange 6).flatMap (fun slot =>
            [(((edge, event), slot), false), (((edge, event), slot), true)]))) := by
  unfold dartEquiv dartCount
  rw [ordered_trans_finCongr, ordered_product, ordered_product, ordered_event]
  simp only [ordered_refl, ordered_bool, List.flatMap_assoc, List.flatMap_map,
    List.map_cons, List.map_nil]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GraphTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTables

open IndependentSetsGames.Foundations.Complexity

def encoding : Computability.Encoding Table Bool where
  encode := tableBits
  decode := decodeTableBits
  decode_encode := decodeTableBits_encoded

theorem tableWords_length_le_bits (table : Table) :
    2 + 4098 * table.darts ≤ (tableBits table).length := by
  rw [tableBits, encodeWords_length, ← tableWords_length]
  omega

end IndependentSetsGames.Foundations.PCP.GraphTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CompareLoop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat} {Λ : Type}

theorem encodeWord_eq_iff (left right : Nat) :
    encodeWord left = encodeWord right ↔ left = right := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
  · rintro rfl
    rfl

def rowLoop (table : GenericGraphTables.Table q) (e : Fin table.darts) : Bool :=
  decide (table.rows[e].tail.val = table.rows[table.rows[e].reverseIndex].tail.val)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_NameCompaction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.NameCompaction

open IndependentSetsGames.Foundations.Target

def evaluationList (F : Formula) (A : Fin F.«variables» → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

def failedCount (F : Formula) (A : Fin F.«variables» → Bool) : Nat :=
  (evaluationList F A).count false

end IndependentSetsGames.Foundations.PCP.NameCompaction

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_InitialGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.InitialGraph

open Target

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩
def variableLabel (value : Bool) : Label := (value, false, false)

def honestLabeling (F : Formula) (A : Fin F.«variables» → Bool) : Vertex F → Label
  | .inl (.inl v) => variableLabel (A v)
  | .inl (.inr i) => fromClauseAnswer (honestAnswer (clauseAt F i) A)
  | .inr _ => variableLabel false

end IndependentSetsGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Minimum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

end Minimum

end IndependentSetsGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_RawInitialTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem table_darts_positive (F : Formula) : 0 < (table F).darts := by
  rw [table_darts]; omega

theorem initial_size (F : Formula) :
    (table F).vertices + (table F).darts = F.«variables» + 7 * F.clauses.length + 2 := by
  rw [table_vertices, table_darts]
  omega

end IndependentSetsGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_RawInitialMachineBudget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

def nameSum {n : Nat} (c : Clause n) : Nat :=
  (c)[0].variableIndex.val + (c)[1].variableIndex.val + (c)[2].variableIndex.val

def bodyTime {n : Nat} (i : Nat) (c : Clause n) : Nat :=
  6 * n + 18 * i + 2 * nameSum c +
    2 * (encodeWords (Complexity.clauseWords c)).length + 63

def loopTime {n : Nat} (i : Nat) : List (Clause n) → Nat
  | [] => 1
  | c :: cs => bodyTime i c + loopTime (i + 1) cs

theorem nameSum_le {n : Nat} (c : Clause n) : nameSum c ≤ 3 * n := by
  have h0 := (c)[0].variableIndex.isLt
  have h1 := (c)[1].variableIndex.isLt
  have h2 := (c)[2].variableIndex.isLt
  unfold nameSum
  omega

def fullBudget (F : Formula) : Nat :=
  6 * F.«variables» + 10 * F.clauses.length + 30 + loopTime 0 F.clauses +
    (GraphTables.tableBits (RawInitialTables.table F)).length

end IndependentSetsGames.Foundations.PCP.RawInitialMachineBudget

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Emitter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open IndependentSetsGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

def bitCommands (bits : List (σ → Bool)) : List (Command h σ bound) := bits.map .bit

theorem bitCommands_bits (bits : List (σ → Bool)) (values : Fin h → Nat) (ambient : σ) :
    (bitCommands (h := h) (bound := bound) bits).flatMap (commandBits values ambient) =
      encodeWords (bits.map (fun bit => if bit ambient then 1 else 0)) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simpa only [bitCommands, List.map_cons, List.flatMap_cons, commandBits, encodeWords]
      using congrArg (encodeWord (if bit ambient then 1 else 0) ++ ·) ih

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Addresses
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

open IndependentSetsGames.Foundations.Hastad
open Enumeration

def eval {bound : Nat} (field : Field bound) (inputs : Fin 5 → Nat) : Nat :=
  Emitter.affineValue field.terms inputs field.offset.val

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Semantics2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Table
variable {q : Nat}

theorem rowList_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.rowList (build input) =
      (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).map
        (rowFromDart input) := by
  change (Vector.ofFn (fun index => rowFromDart input
      ((Enumeration.dartEquiv input.darts q).symm index))).toList =
    (List.ofFn (Enumeration.dartEquiv input.darts q).symm).map (rowFromDart input)
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

theorem tableWords_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
        (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).flatMap
          (fun dart => GraphTables.rowWords (rowFromDart input dart)) := by
  simp only [GraphTables.tableWords, rowList_eq_ordered, build_vertices, build_darts,
    List.flatMap_map]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_EmitRows
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open IndependentSetsGames.Foundations.Complexity
open Emitter

def relationBits (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (Context q → Bool) :=
  List.ofFn fun index : Fin 4096 => fun context =>
    (Relations.relationFromTable context.1 context.2 event slot orientation)[index]

theorem bitValues_ofFn {σ : Type} {n : Nat}
    (relation : σ → Vector Bool n) (context : σ) :
    (List.ofFn (fun index : Fin n => fun state => (relation state)[index])).map
      (fun bit => if bit context then 1 else 0) =
      (relation context).toList.map GraphTables.bitWord := by
  rw [← vector_list_ofFn (relation context)]
  simp only [List.map_ofFn]
  rfl

theorem relationBits_values (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (context : Context q) :
    (relationBits q event slot orientation).map (fun bit => if bit context then 1 else 0) =
      GraphTables.relationWords
        (Relations.relationFromTable context.1 context.2 event slot orientation) := by
  exact bitValues_ofFn (fun state : Context q =>
    Relations.relationFromTable state.1 state.2 event slot orientation) context

def rowContext {q : Nat} (input : GenericGraphTables.Table q) (edge : Fin input.darts) : Context q :=
  let old := input.rows[edge]
  (old.relation, decide (old.tail = input.rows[old.reverseIndex].tail))

def rowValues {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : Fin 5 → Nat :=
  let old := input.rows[edge]
  Addresses.values input.vertices input.darts edge.val old.tail.val
    input.rows[old.reverseIndex].tail.val

theorem encodedRow {n m : Nat} (row : GraphTables.DartRow n m) :
    encodeWords (GraphTables.rowWords row) =
      encodeWord row.tail.val ++ (encodeWord row.reverseIndex.val ++
        encodeWords (GraphTables.relationWords row.relation)) := by
  simp only [GraphTables.rowWords, List.cons_append, List.nil_append, encodeWords]

def blockWords {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : List Nat :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation =>
        GraphTables.rowWords (Table.rowFromDart input (((edge, event), slot), orientation))

theorem tableWords_eq_blocks {q : Nat}
    (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (Table.build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
      (List.finRange input.darts).flatMap (blockWords input) := by
  rw [Table.tableWords_eq_ordered, Enumeration.ordered_dart]
  unfold blockWords
  simp only [List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem encodeWords_flatMap {α : Type} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [encodeWords_append, ih]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Machine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceMachine

open Turing
open IndependentSetsGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

def afterField (source destination : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) : K → List Bool :=
  fieldTapes source destination base suffix (encodeWord n ++ base destination)

end IndependentSetsGames.Foundations.Hastad.SourceMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineUnaryCounter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem counterTapes_other (counter other : K) (hne : other ≠ counter)
    (base : K → List Bool) (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix other = base other := by
  simp [counterTapes, hne]

end IndependentSetsGames.Foundations.Complexity.MachineUnaryCounter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ReadRelation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open IndependentSetsGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev State (σ : Type) (q : Nat) := (σ × RelationTable q) × Option Bool

@[instance_reducible] def stateFintype (σ : Type) (q : Nat) [Fintype σ] :
    Fintype (State σ q) := by
  letI := relationFintype q
  exact inferInstance

def readSlot (source : K) (i : Fin (q * q))
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  .pop source
    (fun state head =>
      ((state.1.1, state.1.2.set i.val (head.getD false) i.isLt), head))
    (.branch (fun state => state.2.getD false)
      (.pop source (fun state _ => (state.1, none)) next)
      (.load (fun state => (state.1, none)) next))

theorem stepAux_readSlot (source : K) (i : Fin (q * q)) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlot source i next) ((ambient, initial), register)
      (Function.update base source (encodeWord (bitWord bit) ++ suffix)) =
      TM2.stepAux next ((ambient, initial.set i.val bit i.isLt), none)
        (Function.update base source suffix) := by
  cases bit <;> simp [readSlot, TM2.stepAux, bitWord, encodeWord]

def readSlots (source : K) : List (Fin (q * q)) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q)
  | [], next => .load (fun state => (state.1, none)) next
  | i :: indices, next => readSlot source i (readSlots source indices next)

def indexedWords (relation : RelationTable q) (indices : List (Fin (q * q))) : List Nat :=
  indices.map (fun i => bitWord relation[i.val])

def fillSlots (relation : RelationTable q) : List (Fin (q * q)) →
    RelationTable q → RelationTable q
  | [], initial => initial
  | i :: indices, initial =>
      fillSlots relation indices (initial.set i.val relation[i.val] i.isLt)

theorem fillSlots_preserves_correct (relation : RelationTable q)
    (indices : List (Fin (q * q))) (initial : RelationTable q) (i : Fin (q * q))
    (hcorrect : initial[i.val] = relation[i.val]) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => exact hcorrect
  | cons j indices ih =>
    apply ih
    by_cases hji : j.val = i.val
    · simp [hji]
    · simp [hji, hcorrect]

theorem fillSlots_mem (relation : RelationTable q) (indices : List (Fin (q * q)))
    (initial : RelationTable q) (i : Fin (q * q)) (hi : i ∈ indices) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => simp at hi
  | cons j indices ih =>
    change (fillSlots relation indices (initial.set j.val relation[j.val] j.isLt))[i.val] = _
    rcases List.mem_cons.mp hi with h | h
    · subst j
      apply fillSlots_preserves_correct
      simp
    · exact ih _ h

theorem fillSlots_finRange (relation initial : RelationTable q) :
    fillSlots relation (List.finRange (q * q)) initial = relation := by
  apply Vector.ext
  intro i hi
  exact fillSlots_mem relation (List.finRange (q * q)) initial ⟨i, hi⟩
    (List.mem_finRange _)

theorem indexedWords_finRange (relation : RelationTable q) :
    indexedWords relation (List.finRange (q * q)) = relationWords relation := by
  have h : (List.finRange (q * q)).map (fun i => relation[i.val]) = relation.toList := by
    rw [List.finRange, List.map_ofFn]
    change List.ofFn (fun i : Fin (q * q) => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  calc
    _ = ((List.finRange (q * q)).map (fun i => relation[i.val])).map bitWord := by
      simp only [indexedWords, List.map_map, Function.comp_def]
    _ = relation.toList.map bitWord := congrArg (fun bits : List Bool => bits.map bitWord) h
    _ = _ := rfl

theorem stepAux_readSlots (source : K) (indices : List (Fin (q * q)))
    (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlots source indices next) ((ambient, initial), register)
      (Function.update base source (encodeWords (indexedWords relation indices) ++ suffix)) =
      TM2.stepAux next ((ambient, fillSlots relation indices initial), none)
        (Function.update base source suffix) := by
  induction indices generalizing initial register with
  | nil => simp [readSlots, fillSlots, indexedWords, encodeWords, TM2.stepAux]
  | cons i indices ih =>
    simp only [readSlots, indexedWords, List.map_cons, encodeWords, List.append_assoc, fillSlots]
    rw [stepAux_readSlot]
    exact ih _ none

def readRelation (source : K)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readSlots source (List.finRange (q * q)) next

theorem stepAux_readRelation (source : K) (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readRelation source next) ((ambient, initial), register)
      (Function.update base source (encodeWords (relationWords relation) ++ suffix)) =
      TM2.stepAux next ((ambient, relation), none) (Function.update base source suffix) := by
  simpa only [readRelation, indexedWords_finRange, fillSlots_finRange] using
    stepAux_readSlots source (List.finRange (q * q)) relation next
      base suffix ambient initial register

def parser (source : K) (exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readRelation source (.goto fun _ => exitLabel)

theorem parserStep (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    TM2.step program
      ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩ =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program readLabel) ((ambient, initial), register)
    (Function.update base source (encodeWords (relationWords relation) ++ suffix))) = _
  rw [atRead, parser, stepAux_readRelation]
  rfl

theorem parserTrace (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩) =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    parserStep source readLabel exitLabel program atRead base relation suffix ambient initial register

end IndependentSetsGames.Foundations.PCP.AlphabetTable.ReadRelation

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Setup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open IndependentSetsGames.Foundations.Complexity
open IndependentSetsGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (ports : Ports K) (base : K → List Bool)
    (n m : Nat) (rows : List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.update base (ports 1) rows)
          (ports 2) (encodeWord n)) (ports 3) (encodeWord m))
      (ports 4) (encodeWord m)) (ports 6) (encodeWord 0)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Setup

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Driver
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopState

open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputBits (input : GenericGraphTables.Table q) : List Bool :=
  GenericGraphTables.tableBits input

def prefixWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q] ++
    ((List.finRange input.darts).take e).flatMap (EmitRows.blockWords input)

def prefixBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (prefixWords input e)

def cursorWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  ((GenericGraphTables.rowList input).drop e).flatMap GenericGraphTables.rowWords

def cursorBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (cursorWords input e)

@[simp] theorem prefixWords_zero (input : GenericGraphTables.Table q) :
    prefixWords input 0 =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  simp [prefixWords]

@[simp] theorem prefixBits_zero (input : GenericGraphTables.Table q) :
    prefixBits input 0 = encodeWords
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  rw [prefixBits, prefixWords_zero]

theorem prefixWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixWords input (e + 1) =
      prefixWords input e ++ EmitRows.blockWords input ⟨e, he⟩ := by
  have bound : e < (List.finRange input.darts).length := by simpa using he
  have take := List.take_succ_eq_append_getElem bound
  have atIndex : (List.finRange input.darts)[e]'bound = (⟨e, he⟩ : Fin input.darts) := by
    simp
  rw [atIndex] at take
  unfold prefixWords
  rw [take, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem prefixBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixBits input (e + 1) =
      prefixBits input e ++ encodeWords (EmitRows.blockWords input ⟨e, he⟩) := by
  rw [prefixBits, prefixWords_succ input e he, encodeWords_append]
  rfl

theorem prefixBits_reverse_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    (prefixBits input (e + 1)).reverse =
      (encodeWords (EmitRows.blockWords input ⟨e, he⟩)).reverse ++
        (prefixBits input e).reverse := by
  rw [prefixBits_succ input e he, List.reverse_append]

theorem prefixWords_full (input : GenericGraphTables.Table q) :
    prefixWords input input.darts = GraphTables.tableWords (Table.build input) := by
  have allRows : (List.finRange input.darts).take input.darts = List.finRange input.darts := by
    apply List.take_of_length_le
    simp
  unfold prefixWords
  rw [allRows]
  exact (EmitRows.tableWords_eq_blocks input).symm

theorem prefixBits_full (input : GenericGraphTables.Table q) :
    prefixBits input input.darts = GraphTables.tableBits (Table.build input) := by
  rw [prefixBits, prefixWords_full]
  rfl

@[simp] theorem cursorBits_zero (input : GenericGraphTables.Table q) :
    cursorBits input 0 =
      encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords) := by
  simp [cursorBits, cursorWords]

theorem cursorWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorWords input e =
      GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)] ++
      cursorWords input (e + 1) := by
  have bound : e < (GenericGraphTables.rowList input).length := by
    simpa only [GenericGraphTables.rowList_length] using he
  unfold cursorWords
  rw [List.drop_eq_getElem_cons bound, List.flatMap_cons]
  simp only [GenericGraphTables.rowList, Vector.getElem_toList, Fin.getElem_fin]

theorem cursorBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorBits input e =
      encodeWords (GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)]) ++
      cursorBits input (e + 1) := by
  rw [cursorBits, cursorWords_succ input e he, encodeWords_append]
  rfl

@[simp] theorem cursorBits_full (input : GenericGraphTables.Table q) :
    cursorBits input input.darts = [] := by
  have finished := List.drop_length (l := GenericGraphTables.rowList input)
  rw [GenericGraphTables.rowList_length] at finished
  unfold cursorBits cursorWords
  rw [finished]
  rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopState

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Initialization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def rowsBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords)

def headerBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Ambient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup
open Turing
open IndependentSetsGames.Foundations.Complexity
open MachineComposition GenericGraphTables
variable {K Λ σ : Type} [DecidableEq K]

def readRowTapes {q n m : Nat} (source tail reverse : K) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source suffix)
    tail (encodeWord row.tail.val)) reverse (encodeWord row.reverseIndex.val)

def readRowCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 5

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_BoundedIteration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BoundedIteration
open Turing
open IndependentSetsGames.Foundations.Complexity

variable {α β : Type}

def counted (count : α → ℕ) (enc : β → List Bool) (start : α → β) (a : α) : List Bool :=
  encodeWord (count a) ++ enc (start a)

lemma count_le (count : α → ℕ) (enc : β → List Bool) (start : α → β) (a : α) :
    count a ≤ (counted count enc start a).length := by
  simp [counted,encodeWord]

noncomputable def certificate (enc : β → List Bool) (step : β → β) (start : α → β)
    (count : α → ℕ) (body : TM2ComputableInPolyTime enc enc step) (length : Polynomial ℕ)
    (growth : ∀ a i, i ≤ count a → (enc (step^[i] (start a))).length ≤
      length.eval (counted count enc start a).length) :
    TM2ComputableInPolyTime (counted count enc start) enc
      (fun a => step^[count a] (start a)) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtime body.time length
  outputsFun a := by
    let words : ℕ → List Bool := fun i => enc (step^[i] (start a))
    let budgets : ℕ → ℕ := fun i => body.time.eval (words i).length
    have runs (i : ℕ) (_hi : i < count a) :
        TM2OutputsInTime body.tm ((words i).map body.inputAlphabet.symm)
          (some ((words (i+1)).map body.outputAlphabet.symm)) (budgets i) := by
      simpa only [words,budgets,Function.iterate_succ_apply',Equiv.symm,Equiv.coe_fn_mk] using
        body.outputsFun (step^[i] (start a))
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count a) words budgets runs
    have start_eq : encodeWord (count a) ++ words 0 = counted count enc start a := rfl
    rw [start_eq] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (counted count enc start a).length
    let L := length.eval N
    let B := body.time.eval L
    have hl (i : ℕ) (hi : i ≤ count a) : (words i).length≤L := growth a i hi
    have hb (i : ℕ) (hi : i < count a) : budgets i≤B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count a) words budgets B L hb hl
    have hc : count a≤N := count_le count enc start a
    rw [runtime_eval]
    calc
      run.steps ≤ count a+1+MachineRepeat.loopBudget (count a) words budgets := run.steps_le_m
      _ ≤ count a+1+(count a*(B+2*L+3)+2*L+3) := Nat.add_le_add_left hloop _
      _ = count a*(B+2*L+4)+2*L+4 := by ring
      _ ≤ N*(B+2*L+4)+2*L+4 := by gcongr

end LargeIndependentSets.BoundedIteration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_SpectralReturn
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

end
end IndependentSetsGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_CayleySpectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open IndependentSetsGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))

variable [Fintype I] [DecidableEq I] [Fintype D]

def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]

theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl

theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

theorem cayley_energy_contraction (g : D → Cube I) (lambda : ℝ) (_hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (f : Cube I → ℝ) (hmean : (𝔼 x, f x) = 0) :
    (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2) := by
  classical
  have hzero : coefficient f zeroFrequency = 0 := by
    rw [coefficient_zeroFrequency]
    exact hmean
  calc
    (𝔼 x, cayleyAverage g f x ^ 2) =
        ∑ s, coefficient (cayleyAverage g f) s ^ 2 := (walsh_parseval _).symm
    _ = ∑ s, (eigenvalue g s * coefficient f s) ^ 2 := by
      simp only [coefficient_cayleyAverage]
    _ ≤ ∑ s, lambda ^ 2 * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = zeroFrequency
      · subst s
        simp [hzero]
      · have hb := hbias s hs
        have hlo : -lambda ≤ eigenvalue g s := (abs_le.mp hb).1
        have hhi : eigenvalue g s ≤ lambda := (abs_le.mp hb).2
        have hprod : 0 ≤ (lambda - eigenvalue g s) * (lambda + eigenvalue g s) :=
          mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
        have hsq : eigenvalue g s ^ 2 ≤ lambda ^ 2 := by nlinarith
        calc
          (eigenvalue g s * coefficient f s) ^ 2 =
              eigenvalue g s ^ 2 * coefficient f s ^ 2 := by rw [mul_pow]
          _ ≤ lambda ^ 2 * coefficient f s ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = lambda ^ 2 * (𝔼 x, f x ^ 2) := by
      rw [← Finset.mul_sum, walsh_parseval]

theorem cayley_spectralCertificate (g : D → Cube I) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambdaone : lambda < 1)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda) :
    SpectralReturn.SpectralCertificate (cayleyGraph g) lambda where
  nonnegative := hlambda
  lt_one := hlambdaone
  contraction := by
    intro f hf
    change (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2)
    exact cayley_energy_contraction g lambda hlambda hbias f hf

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)

end IndependentSetsGames.Foundations.PCP.CayleySpectral
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_CayleyTailCount
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad (bitSign)

variable {α : Type*} [DecidableEq α]

section Words

variable {D : Type*} [Fintype D]

theorem bitSign_mean_eq [Nonempty D] (word : D → Bool) :
    (𝔼 i, bitSign (word i)) =
      1 - 2 * ((countTrue word : ℝ) / Fintype.card D) := by
  have hsign (b : Bool) : bitSign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [bitSign]
  calc
    _ = (𝔼 i : D, (1 - 2 * (if word i = true then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro i _
      exact hsign (word i)
    _ = 1 - 2 * (𝔼 i, if word i = true then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
      rfl

theorem not_badWord_bias (m : ℕ) (hcard : Fintype.card D = 4 * m) (hm : 0 < m)
    (word : D → Bool) (hword : ¬ badWord m word) :
    |𝔼 i, bitSign (word i)| ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Fintype.card D := by rw [hcard]; omega
  let : Nonempty D := Fintype.card_pos_iff.mp hD
  have hlo : m < countTrue word := lt_of_not_ge (not_or.mp hword).1
  have hhi : countTrue word < 3 * m := lt_of_not_ge (not_or.mp hword).2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlor : (m : ℝ) ≤ countTrue word := by exact_mod_cast hlo.le
  have hhir : (countTrue word : ℝ) ≤ 3 * m := by exact_mod_cast hhi.le
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hratioLo : (1 / 4 : ℝ) ≤ (countTrue word : ℝ) / (4 * m) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hratioHi : (countTrue word : ℝ) / (4 * m) ≤ (3 / 4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  rw [bitSign_mean_eq word, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

end Words

end IndependentSetsGames.Foundations.PCP.CayleyTailCount

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Walsh2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.CayleySampling
open scoped BigOperators
open Finset
open IndependentSetsGames.Foundations.Hastad
variable {V D : Type*}

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

end IndependentSetsGames.Foundations.PCP.CayleySampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Expanders
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.Expanders

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad
open CayleySpectral

abbrev Generators (n m : Nat) := Fin (4 * m) → Cube (Fin n)

def badFrequency {n m : Nat} (g : Generators n m) (s : Cube (Fin n)) : ℝ :=
  if s = zeroFrequency then 0 else
    if CayleyTailCount.badWord m (fun d => AssignmentTester.parity s (g d)) then 1 else 0

def badMass {n m : Nat} (g : Generators n m) : ℝ :=
  ∑ s : Cube (Fin n), badFrequency g s

theorem badFrequency_nonnegative {n m : Nat}
    (g : Generators n m) (s : Cube (Fin n)) : 0 ≤ badFrequency g s := by
  unfold badFrequency
  split_ifs <;> norm_num

theorem mean_badFrequency_le {n m : Nat} (s : Cube (Fin n)) :
    (𝔼 g : Generators n m, badFrequency g s) ≤ 2 * (2 / 3 : ℝ) ^ m := by
  classical
  by_cases hs : s = zeroFrequency
  · simp only [badFrequency, ite_eq_left hs, Finset.expect_const_zero]
    positivity
  · have hs' : s ≠ (fun _ => false) := hs
    simp only [badFrequency, ite_eq_right hs]
    rw [CayleySampling.expect_parity_samples s hs'
      (fun w : Fin (4 * m) → Bool => if CayleyTailCount.badWord m w then (1 : ℝ) else 0)]
    exact CayleyTailCount.twoTail_probability m (by simp)

theorem mean_badMass_le (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    (𝔼 g : Generators n m, badMass g) ≤ 1 / 2 := by
  calc
    _ = ∑ s : Cube (Fin n), 𝔼 g : Generators n m, badFrequency g s := by
      unfold badMass
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ _s : Cube (Fin n), 2 * (2 / 3 : ℝ) ^ m :=
      Finset.sum_le_sum (fun s _ => mean_badFrequency_le s)
    _ = (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) := by
      simp [Cube]
    _ ≤ 1 / 2 := CayleyTailCount.union_bound_le_half n m hm

theorem exists_generators (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    ∃ g : Generators n m, ∀ s : Cube (Fin n),
      s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ) := by
  classical
  have hmpos : 0 < m := by omega
  let : Nonempty (Fin (4 * m)) := ⟨⟨0, by omega⟩⟩
  have havg : (𝔼 g : Generators n m, badMass g) < (1 : ℝ) :=
    lt_of_le_of_lt (mean_badMass_le n m hm) (by norm_num)
  obtain ⟨g, _, hg⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty havg
  refine ⟨g, fun s hs => ?_⟩
  have hgood : ¬ CayleyTailCount.badWord m
      (fun d => AssignmentTester.parity s (g d)) := by
    intro hbad
    have hsingle : badFrequency g s ≤ badMass g :=
      Finset.single_le_sum (fun t _ => badFrequency_nonnegative g t) (Finset.mem_univ s)
    simp only [badFrequency, ite_eq_right hs, ite_eq_left hbad] at hsingle
    exact (not_le_of_gt hg) hsingle
  unfold eigenvalue
  simp_rw [← AssignmentTester.bitSign_parity]
  exact CayleyTailCount.not_badWord_bias m (by simp) hmpos _ hgood

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · simpa only [baseDimension, initialDegree, basePower] using CayleyTailCount.seventh_power_size
  · norm_num [basePower]

theorem exists_initial_generators :
    ∃ g : Generators baseDimension initialQuarterDegree,
      ∀ s : Cube (Fin baseDimension), s ≠ zeroFrequency →
        |eigenvalue g s| ≤ (1 / 2 : ℝ) :=
  exists_generators _ _ base_arithmetic.2.1

abbrev BaseVertex := Cube (Fin baseDimension)
abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

theorem exists_baseGraph :
    ∃ H : PoweringWalks.PortGraph BaseVertex BasePort,
      SpectralReturn.SpectralCertificate H (1 / 100 : ℝ) := by
  obtain ⟨g, hg⟩ := exists_initial_generators
  refine ⟨cayleyGraph (powerGenerators g basePower), ?_⟩
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact (power_eigenvalue_bound g (1 / 2) (by norm_num) hg basePower s hs).trans
      base_arithmetic.2.2.2

end IndependentSetsGames.Foundations.PCP.Expanders
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

end IndependentSetsGames.Foundations.PCP.ExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_GraphRounding
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.CloudRounding
open scoped BigOperators
section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

def mismatchSet (G : ConstraintGraph V E A) (ell : E → A) (rounded : V → A) :
    Finset E :=
  Finset.univ.filter (fun e => ell e ≠ rounded (G.tail e))

def copiedRejectionCount (G : ConstraintGraph V E A) (ell : E → A) : Nat :=
  (Finset.univ.filter (fun e => G.accepts e (ell e) (ell (G.reverse e)) = false)).card

def innerDisagreementSet (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) : Finset (E × D) :=
  Finset.univ.filter (fun ed => ell ed.1 ≠ ell (innerRotation G H ed).1)

noncomputable def roundLabels [Nonempty A]
    (G : ConstraintGraph V E A) (ell : E → A) : V → A :=
  fun v => majority (fun e : Cloud G v => ell e.val)

def mismatchFiberEquiv (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (Σ v, ↥(minoritySet (fun e : Cloud G v => ell e.val) (rounded v))) ≃
      ↥(mismatchSet G ell rounded) where
  toFun := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    exact ⟨e, by simpa [mismatchSet, minoritySet] using hbad⟩
  invFun e :=
    ⟨G.tail e.val, ⟨⟨e.val, rfl⟩, by
      simpa [mismatchSet, minoritySet] using e.property⟩⟩
  left_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro e; apply Subtype.ext; rfl

def disagreementFiberEquiv (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (Σ v, ↥(disagreementSet (fun e : Cloud G v => ell e.val)
      (fun ed => ((H v).rot ed).1))) ≃ ↥(innerDisagreementSet G H ell) where
  toFun := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    refine ⟨(e, d), ?_⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  invFun := by
    rintro ⟨⟨e, d⟩, hbad⟩
    refine ⟨G.tail e, ⟨(⟨e, rfl⟩, d), ?_⟩⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  left_inv := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro ed; apply Subtype.ext; rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

end GraphRounding

end IndependentSetsGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Indicators
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

end IndependentSetsGames.Foundations.PCP.SpectralCut
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem rowIndex_val (v d : Nat) (x : Fin v × Fin d) :
    (rowIndex v d x).val = x.2.val + d * x.1.val := rfl

end IndependentSetsGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetGraphBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

end IndependentSetsGames.Foundations.PCP.AlphabetGraphBounds

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Gap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.FinalConstants

def windowSize : Nat := 2 * windowHalf + 1
def walkLength : Nat := 2 * endpointLength + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator
noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

end IndependentSetsGames.Foundations.PCP.FinalConstants

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Contexts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceContexts

open Target PCP

instance clauseAnswerInhabited : Inhabited ClauseAnswer := ⟨⟨false, false, false⟩⟩

instance slotInhabited : Inhabited Slot := ⟨.first⟩

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]

theorem canonicalSlot_name {n : ℕ} (clause : Clause n) (v : Fin n)
    (hv : ∃ s, nameAt clause s = v) : nameAt clause (canonicalSlot clause v) = v := by
  by_cases hfirst : nameAt clause .first = v
  · simp [canonicalSlot, hfirst]
  by_cases hsecond : nameAt clause .second = v
  · simp [canonicalSlot, hfirst, hsecond]
  obtain ⟨s, hs⟩ := hv
  cases s with
  | first => exact False.elim (hfirst hs)
  | second => exact False.elim (hsecond hs)
  | third => simpa [canonicalSlot, hfirst, hsecond] using hs

def pi (F : Formula) {u : ℕ} (c : ClauseContext F u) (v : VariableContext F u)
    (j : J u) : I u :=
  fun t => answerAt (j t) (canonicalSlot (clauseAt F (c t)) (v t))

def honestJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool) : J u :=
  fun t => honestAnswer (clauseAt F (c t)) assignment

def honestI (F : Formula) {u : ℕ} (v : VariableContext F u)
    (assignment : Fin F.«variables» → Bool) : I u :=
  fun t => assignment (v t)

end IndependentSetsGames.Foundations.Hastad.SourceContexts

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Basic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

theorem probability_nonnegative (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    0 ≤ μ.probability event := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonnegative x
  · exact le_rfl

theorem probability_transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ)
    (event : Γ → Bool) :
    (μ.transport equiv).probability event = μ.probability (fun x => event (equiv x)) := by
  unfold probability transport
  exact Fintype.sum_equiv equiv.symm _ _ (fun _ => by simp)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def wins (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂)
    (questions : Q₁ × Q₂) : Bool :=
  G.accepts questions.1 questions.2 (strategy.1 questions.1) (strategy.2 questions.2)

def success (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.questions.probability (G.wins strategy)

def simulatedStrategy {R₁ R₂ B₁ B₂ : Type*}
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (strategy : Strategy R₁ R₂ B₁ B₂) : Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => answerMap₁ x (strategy.1 (questionMap₁ x)),
   fun y => answerMap₂ y (strategy.2 (questionMap₂ y)))

end Game

end

end IndependentSetsGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Value
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

def value (G : Game Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

end Game

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

end FiniteDistribution

end IndependentSetsGames.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Sampling
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

def condition (μ : FiniteDistribution Ω) (given : Ω → Bool)
    (positive : 0 < μ.probability given) : FiniteDistribution Ω where
  weight x := if given x then μ.weight x / μ.probability given else 0
  nonnegative x := by
    split
    · exact div_nonneg (μ.nonnegative x) positive.le
    · exact le_rfl
  normalized := by
    calc
      _ = (∑ x, if given x then μ.weight x else 0) / μ.probability given := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : given x = true <;> simp [hx]
      _ = 1 := div_self (ne_of_gt positive)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

theorem selectedSuccess_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : 0 ≤ G.selectedSuccess strategy selected :=
  (G.repetition n).questions.probability_nonnegative _

end Game

end IndependentSetsGames.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Game
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

def repeatedVisible (F : Formula) (u : ℕ) (events : Fin u → RandomEvent F) :
    VariableContext F u × ClauseContext F u :=
  (fun t => nameAt (clauseAt F (events t).1) (events t).2,
   fun t => (events t).1)

end IndependentSetsGames.Foundations.Hastad.SourceGame

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_VerifierCNF
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.VerifierToCNF

open Target

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

theorem convert_nonempty {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (eventsPositive : 0 < V.events) : (convert V hq).clauses ≠ [] := by
  have p : 0 < (convert V hq).clauses.length := by
    rw [convert_clause_count]
    exact Nat.mul_pos eventsPositive (Nat.mul_pos (Nat.pow_pos (by decide)) (by omega))
  intro empty
  simp only [empty, List.length_nil] at p
  omega

end IndependentSetsGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_FinalBooleanVerifier
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

@[simp] theorem bitsOfLabels_labelsOfBits (vertices : V ≃ Fin n)
    (assignment : Fin (n * 6) → Bool) : bitsOfLabels vertices (labelsOfBits vertices assignment) = assignment := by
  funext k
  simp only [bitsOfLabels, labelsOfBits, bitIndex, Equiv.apply_symm_apply, Prod.eta]

abbrev OutputAssignment (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) :=
  Fin (VerifierToCNF.outputVariables (verifier G vertices edges)) → Bool

def extractLabeling (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) : V → Label :=
  labelsOfBits vertices (VerifierToCNF.restrictAssignment (verifier G vertices edges) assignment)

theorem cnf_nonempty (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (nonempty : 0 < m) : (cnf G vertices edges).clauses ≠ [] :=
  VerifierToCNF.convert_nonempty (verifier G vertices edges) (by decide) nonempty

end IndependentSetsGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_KernelSampling
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators
noncomputable section

namespace KernelSampling

def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

end KernelSampling
end
end IndependentSetsGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Conditionals
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem conditionalKernel_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (a : α) :
    IsProbability (conditionalKernel p fallback a) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · simpa only [IsProbability, conditionalKernel, ite_eq_left hm] using hf
  · constructor
    · intro b
      simp only [conditionalKernel, ite_eq_right hm]
      exact div_nonneg (hp.1 (a, b))
        ((firstMarginal_isProbability p hp).1 a)
    · simp only [conditionalKernel, ite_eq_right hm, div_eq_mul_inv, ← Finset.sum_mul]
      change firstMarginal p a * (firstMarginal p a)⁻¹ = 1
      exact mul_inv_cancel₀ hm

theorem marginal_mul_conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (a : α) (b : β) :
    firstMarginal p a * conditionalKernel p fallback a b = p (a, b) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · have hpoint := point_le_firstMarginal p hp a b
    rw [hm] at hpoint
    have hz : p (a, b) = 0 := le_antisymm hpoint (hp.1 (a, b))
    simp [conditionalKernel, hm, hz]
  · simp only [conditionalKernel, ite_eq_right hm]
    calc
      firstMarginal p a * (p (a, b) / firstMarginal p a)
          = p (a, b) *
              (firstMarginal p a / firstMarginal p a) := by ring
      _ = p (a, b) := by rw [div_self hm, mul_one]

end IndependentSetsGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_TotalVariation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

def totalVariation (μ ν : FiniteDistribution Ω) : ℝ :=
  (∑ x, |μ.weight x - ν.weight x|) / 2

end
end IndependentSetsGames.Foundations.Games.FiniteDistribution

namespace IndependentSetsGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem gameLaw_isProbability (μ : Games.FiniteDistribution α) : IsProbability μ.weight :=
  ⟨μ.nonnegative, μ.normalized⟩

def toGameLaw (p : α → ℝ) (hp : IsProbability p) : Games.FiniteDistribution α where
  weight := p
  nonnegative := hp.1
  normalized := hp.2

noncomputable def gameConditionalKernel (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) : Games.FiniteDistribution β :=
  toGameLaw (conditionalKernel μ.weight fallback.weight a)
    (conditionalKernel_isProbability μ.weight fallback.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) a)

theorem gameConditionalKernel_recombine (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) (b : β) :
    firstMarginal μ.weight a * (gameConditionalKernel μ fallback a).weight b =
      μ.weight (a, b) :=
  marginal_mul_conditionalKernel μ.weight fallback.weight (gameLaw_isProbability μ) a b

end IndependentSetsGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Reveal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X × Y) × (X ⊕ Y)) :=
  (μ.product (FiniteDistribution.uniform Bool)).pushforward
    (fun z => (z.1, revealEndpoint z.1 z.2))

theorem revealLaw_weight (μ : FiniteDistribution (X × Y)) (q : X × Y) (r : X ⊕ Y) :
    (revealLaw μ).weight (q,r) =
      (if r = Sum.inl q.1 then μ.weight q / 2 else 0) +
      (if r = Sum.inr q.2 then μ.weight q / 2 else 0) := by
  classical
  rcases q with ⟨x,y⟩
  simp only [revealLaw, FiniteDistribution.pushforward, FiniteDistribution.product,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [revealEndpoint, FiniteDistribution.uniform, div_eq_mul_inv, add_comm, eq_comm]

def revealFirstLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X ⊕ Y) × (X × Y)) :=
  (revealLaw μ).transport (Equiv.prodComm _ _)

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem revealFirstLaw_weight (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealFirstLaw μ).weight (r,q) = (revealLaw μ).weight (q,r) := rfl

def revealFallback (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  match r with
  | Sum.inl x => μ.pushforward (fun q => (x,q.2))
  | Sum.inr y => μ.pushforward (fun q => (q.1,y))

def revealProfile (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  gameConditionalKernel (revealFirstLaw μ) (revealFallback μ r) r

def revealInputLaw (μ : FiniteDistribution (X × Y)) : FiniteDistribution (X ⊕ Y) :=
  (revealLaw μ).pushforward Prod.snd

theorem revealInputLaw_weight (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    (revealInputLaw μ).weight r = firstMarginal (revealFirstLaw μ).weight r := by
  classical
  cases r <;>
    simp [revealInputLaw, FiniteDistribution.pushforward, firstMarginal, Fintype.sum_prod_type]

theorem reveal_profile_recombination (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealInputLaw μ).weight r * (revealProfile μ r).weight q =
      (revealLaw μ).weight (q,r) := by
  rw [revealInputLaw_weight]
  exact gameConditionalKernel_recombine (revealFirstLaw μ) (revealFallback μ r) r q

theorem revealLaw_sum_left (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ x, (revealLaw μ).weight (q, Sum.inl x)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem revealLaw_sum_right (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ y, (revealLaw μ).weight (q, Sum.inr y)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem reveal_product_factorization {ι : Type*} [Fintype ι]
    (μ : FiniteDistribution (X × Y)) (r : ι → X ⊕ Y) (q : ι → X × Y) :
    (∏ i, (revealInputLaw μ).weight (r i)) *
      (∏ i, (revealProfile μ (r i)).weight (q i)) =
        ∏ i, (revealLaw μ).weight (q i,r i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact reveal_profile_recombination μ (r i) (q i)

theorem reveal_product_forget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (q : ι → X × Y) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        (∏ i, (revealProfile μ (r i)).weight (q i))) =
      ∏ i, μ.weight (q i) := by
  classical
  simp_rw [reveal_product_factorization]
  calc
    _ = ∏ i, ∑ r : X ⊕ Y, (revealLaw μ).weight (q i,r) :=
      (Fintype.prod_sum (fun (i : ι) (r : X ⊕ Y) => (revealLaw μ).weight (q i,r))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_sum_type, revealLaw_sum_left, revealLaw_sum_right]
      ring

theorem reveal_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (f : (ι → X × Y) → ℝ) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        ∑ q : ι → X × Y, (∏ i, (revealProfile μ (r i)).weight (q i)) * f q) =
      ∑ q : ι → X × Y, (∏ i, μ.weight (q i)) * f q := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [reveal_product_forget]

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_MaskedVariation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (maskedJoint p) z.1 * (revealProfile μ z.1.2).weight z.2

def leftRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ y, p (z.1, (z.2.1, y))) * (revealProfile μ (Sum.inl z.2.1)).weight z.2

def rightRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ x, p (z.1, (x, z.2.2))) * (revealProfile μ (Sum.inr z.2.2)).weight z.2

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_PartialReveal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def partialRevealWeight (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) : ℝ :=
  μ.weight (u j) * ∏ i : {i : I // i ≠ j}, (revealLaw μ).weight (u i.1,rest i)

theorem product_reveal_at (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (r : X ⊕ Y) (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    (∏ i, (revealLaw μ).weight (u i,mergeAt j r rest i)) =
      (if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
      (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [mergeAt_self, mergeAt_other, revealLaw_weight]
  by_cases hl : r = Sum.inl (u j).1 <;> by_cases hr : r = Sum.inr (u j).2 <;>
    simp [hl, hr, partialRevealWeight, revealLaw_weight] <;> ring

def partialRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    partialRevealWeight μ j z.1.2 u * likelihood z.1.1 u else 0

def fullRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    (∏ i, (revealLaw μ).weight (u i,z.1.2 i)) * likelihood z.1.1 u else 0

omit [Fintype T] in
theorem fullRevealMarginal_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealMarginal μ j likelihood ((t,mergeAt j r rest),q) =
      maskedJoint (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  classical
  unfold fullRevealMarginal
  simp_rw [product_reveal_at]
  have hpoint (u : I → X × Y) :
      (if u j = q then
        ((if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
         (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0)) *
          likelihood t u else 0) =
      (if r = Sum.inl q.1 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) +
      (if r = Sum.inr q.2 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) := by
    by_cases hu : u j = q
    · rw [hu]
      by_cases hl : r = Sum.inl q.1 <;> by_cases hr : r = Sum.inr q.2 <;>
        simp [hl, hr] <;> ring
    · simp [hu]
  simp_rw [hpoint]
  simp [maskedJoint, partialRevealMarginal, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]

def fullRevealModel (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (fullRevealMarginal μ j likelihood) z.1 *
    (revealProfile μ (z.1.2 j)).weight z.2

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedInformation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem iid_coordinate_split {Ω : Type*} [Fintype Ω] {n : Nat}
    (μ : FiniteDistribution Ω) (selected : Finset (Fin n)) :
    (μ.iid n).transport (coordinateSplitEquiv selected) =
      (FiniteDistribution.table (fun _ : selected => μ)).product
        (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => μ)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, μ.weight (mergeCoordinates selected x.1 x.2 i)) =
    (∏ i : selected, μ.weight (x.1 i)) *
      ∏ i : {i : Fin n // i ∉ selected}, μ.weight (x.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ selected)
    (fun i => μ.weight (mergeCoordinates selected x.1 x.2 i))
  have hi : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : {i : Fin n // i ∈ selected},
        μ.weight (mergeCoordinates selected x.1 x.2 i.1)) *
        ∏ i : {i : Fin n // i ∉ selected},
          μ.weight (mergeCoordinates selected x.1 x.2 i.1) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedAnswerLabel
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    SelectedLabels (A₁ := A₁) (A₂ := A₂) selected :=
  (fun i => strategy.1 questions.1 i.1, fun i => strategy.2 questions.2 i.1)

def selectedLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ := by
  classical
  let questions := selectedQuestionTuple selected fixed remaining
  exact if selectedAnswerLabel strategy selected questions = label then
    (if G.selectedWins strategy selected questions then 1 else 0) else 0

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    0 ≤ selectedLikelihood G strategy selected fixed label remaining := by
  classical
  dsimp only [selectedLikelihood]
  split_ifs <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) =
      if G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining)
      then 1 else 0 := by
  classical
  simp [selectedLikelihood]

def selectedSplitLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution ((selected → Q₁ × Q₂) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => G.questions))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (selectedSplitLaw G selected).probability
      (fun q => G.selectedWins strategy selected (selectedQuestionTuple selected q.1 q.2)) =
        G.selectedSuccess strategy selected := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability _
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

def selectedInputLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution (SelectedInput Q₁ Q₂ selected) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => revealInputLaw G.questions))

def selectedInputProfile (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (t : SelectedInput Q₁ Q₂ selected) (i : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (Q₁ × Q₂) := revealProfile G.questions (t.2 i)

def selectedSideMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  ∑ u, independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
    selectedLikelihood G strategy selected tv.1.1 tv.2 u

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSideMass_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (t : SelectedInput Q₁ Q₂ selected) :
    (∑ v, selectedSideMass G strategy selected (t,v)) =
      ∑ u, independentProduct (fun i => (selectedInputProfile G selected t i).weight) u *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u)
        then 1 else 0) := by
  classical
  simp only [selectedSideMass]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, selectedLikelihood_sum]

theorem selectedSideMass_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ tv, (selectedInputLaw G selected).weight tv.1 *
      selectedSideMass G strategy selected tv) = G.selectedSuccess strategy selected := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, selectedSideMass_sum]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u)
        then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_probability G strategy selected
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

def selectedSideWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  (selectedInputLaw G selected).weight tv.1 * selectedSideMass G strategy selected tv /
    G.selectedSuccess strategy selected

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedJoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

section
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedJointWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (z : (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) : ℝ :=
  (selectedInputLaw G selected).weight z.1.1 *
    independentProduct (fun i => (selectedInputProfile G selected z.1.1 i).weight) z.2 *
      selectedLikelihood G strategy selected z.1.1.1 z.1.2 z.2 /
        G.selectedSuccess strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (z) : 0 ≤ selectedJointWeight G strategy selected z := by
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg ((selectedInputLaw G selected).nonnegative _)
        ((independentProduct_isProbability _
          (fun i => gameLaw_isProbability (selectedInputProfile G selected z.1.1 i))).1 z.2))
      (selectedLikelihood_nonnegative G strategy selected z.1.1.1 z.1.2 z.2)
  · exact G.selectedSuccess_nonnegative strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) :
    firstMarginal (selectedJointWeight G strategy selected) tv =
      selectedSideWeight G strategy selected tv := by
  simp only [firstMarginal, selectedJointWeight, selectedSideWeight, selectedSideMass,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem selectedJointWeight_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    IsProbability (selectedJointWeight G strategy selected) := by
  constructor
  · exact selectedJointWeight_nonnegative G strategy selected
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedJointWeight G strategy selected) tv) = 1
    simp_rw [selectedJointWeight_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedJointLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :=
  toGameLaw (selectedJointWeight G strategy selected)
    (selectedJointWeight_isProbability G strategy selected positive)

theorem selectedJointWeight_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) (u) :
    selectedJointWeight G strategy selected (tv,u) =
      (∏ i : selected, G.questions.weight (tv.1.1 i)) *
        (∏ i : {i : Fin n // i ∉ selected}, (revealLaw G.questions).weight (u i,tv.1.2 i)) *
          selectedLikelihood G strategy selected tv.1.1 tv.2 u /
            G.selectedSuccess strategy selected := by
  unfold selectedJointWeight
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    independentProduct, selectedInputProfile]
  rw [mul_assoc (∏ i : selected, G.questions.weight (tv.1.1 i)), reveal_product_factorization]

end
end

open scoped BigOperators
open Information

end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedMarginal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedRawMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then selectedJointWeight G strategy selected (z.1,u) else 0

theorem selectedRawMarginal_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) :
    firstMarginal (selectedRawMarginal G strategy selected j) tv =
      selectedSideWeight G strategy selected tv := by
  classical
  simp only [firstMarginal, selectedRawMarginal]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact selectedJointWeight_firstMarginal G strategy selected tv

theorem selectedRawMarginal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (selectedRawMarginal G strategy selected j) := by
  classical
  constructor
  · intro z
    apply Finset.sum_nonneg
    intro u _
    split
    · exact selectedJointWeight_nonnegative G strategy selected (z.1,u)
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedRawMarginal G strategy selected j) tv) = 1
    simp_rw [selectedRawMarginal_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedOutsideLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ :=
  (∏ i : selected, G.questions.weight (t.1 i)) *
    selectedLikelihood G strategy selected t.1 t.2 u / G.selectedSuccess strategy selected

theorem selectedRawMarginal_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    selectedRawMarginal G strategy selected j
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  classical
  change selectedRawMarginal G strategy selected j
    (((z.1.1.1,z.1.2),z.1.1.2),z.2) = _
  simp only [selectedRawMarginal, fullRevealMarginal]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = z.2
  · simp only [ite_eq_left hu, selectedJointWeight_factorization, selectedOutsideLikelihood]
    ring
  · simp [hu]

def selectedInformationRadius (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
    (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
      Real.log (1 / G.selectedSuccess strategy selected)))

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Mixture
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Games.FiniteDistribution

section

open scoped BigOperators

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

def mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) : FiniteDistribution Ω where
  weight x := ∑ seed, seedLaw.weight seed * (laws seed).weight x
  nonnegative x := Finset.sum_nonneg fun seed _ =>
    mul_nonneg (seedLaw.nonnegative seed) ((laws seed).nonnegative x)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (laws _).normalized, mul_one]
    exact seedLaw.normalized

end

open scoped BigOperators

end IndependentSetsGames.Foundations.Games.FiniteDistribution
namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information

theorem partialRevealMarginal_isProbability
    {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ)
    (hp : IsProbability (fullRevealMarginal μ j likelihood)) :
    IsProbability (partialRevealMarginal μ j likelihood) := by
  apply (maskedJoint_isProbability_iff _).mp
  have h := isProbability_comp_equiv (revealSplitEquiv (T := T) j).symm _ hp
  have he : (fun z => fullRevealMarginal μ j likelihood
      ((revealSplitEquiv (T := T) j).symm z)) =
      maskedJoint (partialRevealMarginal μ j likelihood) := by
    funext z
    exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
  rw [he] at h
  exact h

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_fullReveal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) := by
  have h := isProbability_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm
    _ (selectedRawMarginal_isProbability G strategy selected positive j)
  have he : (fun z => selectedRawMarginal G strategy selected j
      ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z)) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) := by
    funext z
    exact selectedRawMarginal_fullReveal G strategy selected j z
  rw [he] at h
  exact h

def selectedCommonLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j × (Q₁ × Q₂)) :=
  toGameLaw (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
    (partialRevealMarginal_isProbability G.questions j _
      (selected_fullReveal_isProbability G strategy selected positive j))

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_TraceLaw
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.CorrelatedSampling

def splitLeft (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨I.lo, splitPoint I t, le_max_left _ _⟩

def splitRight (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨splitPoint I t, I.hi, max_le I.valid (min_le_right _ _)⟩

def cutAt (r : ℝ) (I : ThresholdInterval) : Prop := I.hi ≤ r ∨ r ≤ I.lo

def intervalCDF (r : ℝ) (I : ThresholdInterval) : ℝ := min r I.hi - min r I.lo

def splitAll (t : ℝ) : List ThresholdInterval → List ThresholdInterval
  | [] => []
  | I :: rest => splitLeft I t :: splitRight I t :: splitAll t rest

def unitThresholdInterval : ThresholdInterval := ⟨0, 1, by norm_num⟩

def thresholdPartition : List ℝ → List ThresholdInterval
  | [] => [unitThresholdInterval]
  | t :: rest => splitAll t (thresholdPartition rest)

def sumOnIntervals (f : ThresholdInterval → ℝ) : List ThresholdInterval → ℝ
  | [] => 0
  | I :: rest => f I + sumOnIntervals f rest

theorem sumOn_splitAll (f : ThresholdInterval → ℝ) (t : ℝ)
    (hf : ∀ I, f (splitLeft I t) + f (splitRight I t) = f I)
    (intervals : List ThresholdInterval) :
    sumOnIntervals f (splitAll t intervals) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => rfl
  | cons I rest ih =>
      simp only [splitAll, sumOnIntervals, ih]
      rw [← add_assoc, hf]

theorem partition_sum (f : ThresholdInterval → ℝ)
    (hf : ∀ t I, f (splitLeft I t) + f (splitRight I t) = f I)
    (thresholds : List ℝ) :
    sumOnIntervals f (thresholdPartition thresholds) = f unitThresholdInterval := by
  induction thresholds with
  | nil => simp [thresholdPartition, sumOnIntervals]
  | cons t rest ih =>
      rw [thresholdPartition, sumOn_splitAll f t (hf t), ih]

theorem partition_total_mass (thresholds : List ℝ) :
    sumOnIntervals (fun I => I.hi - I.lo) (thresholdPartition thresholds) = 1 := by
  have h := partition_sum (fun I => I.hi - I.lo)
    (fun t I => by simp only [splitLeft, splitRight]; ring) thresholds
  simpa [unitThresholdInterval] using h

theorem sum_interval_get (f : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∑ i : Fin intervals.length, f intervals[i]) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => simp [sumOnIntervals]
  | cons I rest ih =>
      simpa [Fin.sum_univ_succ, sumOnIntervals] using congrArg (fun x : ℝ => f I + x) ih

end IndependentSetsGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Rectangle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.CorrelatedSampling

section

variable {α : Type*} [Fintype α]

abbrev RectangleSeed (thresholds : List ℝ) (α : Type*) :=
  α × Fin (thresholdPartition thresholds).length

def rectangleWeight (thresholds : List ℝ) (seed : RectangleSeed thresholds α) : ℝ :=
  ((thresholdPartition thresholds)[seed.2].hi - (thresholdPartition thresholds)[seed.2].lo) /
    (Fintype.card α : ℝ)

def rectangleAccept (thresholds : List ℝ) (density : α → ℝ)
    (seed : RectangleSeed thresholds α) : Bool :=
  decide ((thresholdPartition thresholds)[seed.2].lo < density seed.1)

theorem rectangleWeight_nonnegative (thresholds : List ℝ) (seed : RectangleSeed thresholds α) :
    0 ≤ rectangleWeight thresholds seed :=
  div_nonneg (sub_nonneg.mpr ((thresholdPartition thresholds)[seed.2].valid)) (by positivity)

theorem rectangleWeight_normalized [Nonempty α] (thresholds : List ℝ) :
    ∑ seed : RectangleSeed thresholds α, rectangleWeight thresholds seed = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow (a : α) : (∑ i, rectangleWeight thresholds (a, i)) =
      1 / (Fintype.card α : ℝ) := by
    unfold rectangleWeight
    rw [← sum_div_const, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
  simp_rw [hrow]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

def rectangleDistribution [Nonempty α] (thresholds : List ℝ) :
    Games.FiniteDistribution (RectangleSeed thresholds α) where
  weight := rectangleWeight thresholds
  nonnegative := rectangleWeight_nonnegative thresholds
  normalized := rectangleWeight_normalized thresholds

end

end IndependentSetsGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Rectangle2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.CorrelatedSampling

open scoped BigOperators

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) : List ℝ :=
  profileThresholds (fun (k : Q₁ ⊕ Q₂) s => (Sum.elim L R k).weight s)

abbrev SharedProfileSeed (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) :=
  RectangleSeed (sharedProfileThresholds L R) S

def sharedProfileLeft (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (L x).weight

def sharedProfileRight (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (R y).weight

def sharedProfileReject (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (y : Q₂) : ℝ :=
  eventMass (rectangleWeight (sharedProfileThresholds L R))
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s))

end IndependentSetsGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SharedSampling
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_DistributionIdentities
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

end Diagonal

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

end
end IndependentSetsGames.Foundations.Repetition.CompletedSampling

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_CoordinateCompletion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition.CompletedSampling
open scoped BigOperators
open Games

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

end IndependentSetsGames.Foundations.Repetition.CompletedSampling

namespace IndependentSetsGames.Foundations.Games.Game

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Seed : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Seed]
  [Nonempty A₁] [Nonempty A₂]

def localEmbeddingLaw (G : Game Q₁ Q₂ A₁ A₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂) :
    FiniteDistribution (R₁ × R₂) :=
  seedLaw.mixture fun seed =>
    G.questions.pushforward fun q => (left seed q.1, right seed q.2)

def coordinateGame (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂))) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) where
  questions := law
  accepts x y a b := G.accepts (x coordinate) (y coordinate) (a coordinate) (b coordinate)

end IndependentSetsGames.Foundations.Games.Game

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_Completion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

def normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) : FiniteDistribution X :=
  if h : 0 < ∑ x, w x then
    { weight := normalizedWeight w
      nonnegative := (normalizedWeight_isProbability w hw h).1
      normalized := (normalizedWeight_isProbability w hw h).2 }
  else fallback

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ProfileBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem leftCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (x : X) :
    IsProbability (leftCommonProfile p fallback x) :=
  conditionalKernel_isProbability _ _ (leftCommonMarginal_isProbability p hp) hf x

theorem rightCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (y : Y) :
    IsProbability (rightCommonProfile p fallback y) :=
  leftCommonProfile_isProbability (fun z => p (swapQuestionEndpoints z)) fallback
    (isProbability_comp_equiv swapQuestionEndpoints p hp) hf y

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_QuestionMarginal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Games Information

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedTupleLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) : ℝ :=
  if G.selectedWins strategy selected (Game.tupleQuestionEquiv n questions) then 1 else 0

def selectedQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) : FiniteDistribution (Q₁ × Q₂) :=
  ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).pushforward
    (fun questions => (questions.1 i, questions.2 i))

end

end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedProfiles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition

section
open scoped BigOperators
open Games Information

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

end

open scoped BigOperators
open Games Information

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedProfileBudget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition

section
open scoped BigOperators
open Games Information
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedEmbeddingError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  2 * selectedLeftProfileError G strategy selected positive j +
    2 * selectedRightProfileError G strategy selected positive j

end
open Games
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLabelAccepts (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : Bool := by
  classical
  exact decide (∀ i : selected, G.accepts (fixed i).1 (fixed i).2 (label.1 i) (label.2 i) = true)

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_RevealFactorization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition

section
open scoped BigOperators
open Games
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLeftFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (x : X) : ℝ :=
  match r with
  | Sum.inl u => if x = u then 1 else 0
  | Sum.inr v => μ.weight (x,v) / 2

def revealRightFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (y : Y) : ℝ :=
  match r with
  | Sum.inl u => μ.weight (u,y) / 2
  | Sum.inr v => if y = v then 1 else 0

omit [DecidableEq Y] in
theorem revealLeftFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) : 0 ≤ revealLeftFactor μ r x := by
  cases r with
  | inl u => simp only [revealLeftFactor]; split <;> norm_num
  | inr v => exact div_nonneg (μ.nonnegative _) (by norm_num)

omit [DecidableEq X] in
theorem revealRightFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (y : Y) : 0 ≤ revealRightFactor μ r y := by
  cases r with
  | inl u => exact div_nonneg (μ.nonnegative _) (by norm_num)
  | inr v => simp only [revealRightFactor]; split <;> norm_num

def partialLeftFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (x : I → X) : ℝ :=
  ∏ i, revealLeftFactor μ (rest i) (x i.1)

def partialRightFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (y : I → Y) : ℝ :=
  ∏ i, revealRightFactor μ (rest i) (y i.1)

end

open scoped BigOperators
open Games

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def updatedTableFallback (μ : FiniteDistribution X) (j : I) (x : X) :
    FiniteDistribution (I → X) :=
  (FiniteDistribution.table (fun _ : I => μ)).pushforward
    (fun l => Function.update l j x)

end LocalNormalization

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLeftRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) : ℝ :=
  (if l j = x then 1 else 0) * partialLeftFactor G.questions j s.2 l *
    selectedLocalTest strategy.1 selected (fun i => (s.1.1 i).1) s.1.2.1 l

def selectedRightRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) : ℝ :=
  (if r j = y then 1 else 0) * partialRightFactor G.questions j s.2 r *
    selectedLocalTest strategy.2 selected (fun i => (s.1.1 i).2) s.1.2.2 r

omit [DecidableEq Q₂] in
theorem selectedLeftRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) :
    0 ≤ selectedLeftRaw G strategy selected j s x l := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealLeftFactor_nonnegative G.questions (s.2 i) (l i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

omit [DecidableEq Q₁] in
theorem selectedRightRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) :
    0 ≤ selectedRightRaw G strategy selected j s y r := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealRightFactor_nonnegative G.questions (s.2 i) (r i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

def selectedLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₁) :=
  normalizeOr (selectedLeftRaw G strategy selected j s x)
    (selectedLeftRaw_nonnegative G strategy selected j s x)
    (updatedTableFallback (G.questions.pushforward Prod.fst) j x)

def selectedRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₂) :=
  normalizeOr (selectedRightRaw G strategy selected j s y)
    (selectedRightRaw_nonnegative G strategy selected j s y)
    (updatedTableFallback (G.questions.pushforward Prod.snd) j y)

def selectedCompletionScale (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) : ℝ :=
  G.questions.weight xy * (∏ i : selected, G.questions.weight (s.1.1 i)) *
    (if selectedLabelAccepts G selected s.1.1 s.1.2 then 1 else 0) /
      G.selectedSuccess strategy selected

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedCompletionGame
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedFullLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₁) :=
  (selectedLeftCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).1))

def selectedFullRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₂) :=
  (selectedRightCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).2))

def selectedFullCompletionMixture (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)) :=
  ((selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)).mixture
    (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
      (selectedFullRightCompletion G strategy selected j (z.1.2,z.2)))

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ActualGame
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition.SelectionSequence
open IndependentSetsGames.Foundations.Games

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
variable [Nonempty A₁] [Nonempty A₂]

def ConditionalCoordinateBound (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (_hcard : S.card < n)
    (hp : 0 < G.selectedSuccess strategy S),
    ∃ j, j ∉ S ∧
      (((G.repetition n).questions.condition (G.selectedWins strategy S) hp).probability
        (G.coordinateWin strategy j)) ≤
        G.value + 15 * Real.sqrt
          (((S.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy S)) /
            ((n : ℝ) - S.card))

end IndependentSetsGames.Foundations.Repetition.SelectionSequence

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Gap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceGame
open IndependentSetsGames.Integration.SourceParameters
open IndependentSetsGames.Reduction

def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.«variables» → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

end IndependentSetsGames.Foundations.Hastad.SourceGap

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AmplificationIteration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AmplificationIteration

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

end IndependentSetsGames.Foundations.PCP.AmplificationIteration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AmplificationRound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6

end IndependentSetsGames.Foundations.PCP.AmplificationRound
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_RoundGap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

end IndependentSetsGames.Foundations.PCP.RoundGap

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_PCPIteration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.PCPIteration

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

end IndependentSetsGames.Foundations.PCP.PCPIteration
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LabelCoverData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

def mixedProject {L R : Type*} {n : ℕ} (h : Fin n) (π : L → R)
    (x : MixedTuple L R n h.val) : MixedTuple L R n (h.val + 1) :=
  ⟨fun k => if k = h then Sum.inl ((x.val k).elim id π) else x.val k, by
    intro k
    by_cases hk : k = h
    · subst k
      simp
    · simp only [ite_eq_right hk, x.property k]
      have hne : k.val ≠ h.val := fun e => hk (Fin.ext e)
      have he : (k.val < h.val) = (k.val < h.val + 1) := propext (by omega)
      simp only [he]⟩

inductive LayerImposed {U V L R C : Type*} (lc : LabelCoverData U V L R C) (n : ℕ) :
    (q q' : LayerQuestion U V n) → (LayerAnswer L R q → LayerAnswer L R q') → Prop
  | adjacent (h : Fin n) (q : MixedTuple U V n h.val)
      (q' : MixedTuple U V n (h.val + 1)) (c : C)
      (hleft : q.val h = Sum.inr (lc.left c))
      (hright : q'.val h = Sum.inl (lc.right c))
      (houtside : ∀ k, k ≠ h → q.val k = q'.val k) :
      LayerImposed lc n ⟨h.castSucc, q⟩ ⟨h.succ, q'⟩ (mixedProject h (lc.project c))

def layeredSystem {U V L R C : Type*} (lc : LabelCoverData U V L R C) (n : ℕ) :
    ProjectionSystem (LayerQuestion U V n) (LayerAnswer L R) where
  imposed := LayerImposed lc n

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FrameNonempty
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.LCInput
open IndependentSetsGames.Foundations
open Target PCP Hastad.SourceContexts Hastad.SourceGame Games
open scoped BigOperators Classical
noncomputable section

def fallback {n : ℕ} (cl : Target.Clause n) : ClauseAnswer :=
  honestAnswer cl (fun v => if v = cl[0].variableIndex then cl[0].positive else false)

lemma fallback_satisfies {n : ℕ} (cl : Target.Clause n) : localSatisfies cl (fallback cl) = true := by
  simp only [fallback, honest_satisfies, Target.Clause.eval, Target.Literal.eval]
  cases cl[0].positive <;> simp

lemma honest_consistent {n : ℕ} (cl : Target.Clause n) (a : Fin n → Bool) :
    localConsistent cl (honestAnswer cl a) = true := by
  rw [localConsistent_eq_true_iff]
  intro s s' h
  simpa only [honest_answerAt] using congrArg a h

lemma fallback_consistent {n : ℕ} (cl : Target.Clause n) : localConsistent cl (fallback cl) = true :=
  honest_consistent cl _

def repair {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) : ClauseAnswer :=
  if localSatisfies cl j = true ∧ localConsistent cl j = true then j else fallback cl

lemma repair_spec {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) :
    localSatisfies cl (repair cl j) = true ∧ localConsistent cl (repair cl j) = true := by
  unfold repair
  split
  · assumption
  · exact ⟨fallback_satisfies cl, fallback_consistent cl⟩

def repaired (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) (j : J u) : J u :=
  fun t => repair (clauseAt F (c t)) (j t)

def labelCover (F : Target.Formula) (u : ℕ) :
    LabelCoverData (ClauseContext F u) (VariableContext F u) (J u) (I u)
      (Fin u → RandomEvent F) where
  left e := fun t => (e t).1
  right e := (repeatedVisible F u e).1
  project e j := pi F (fun t => (e t).1) (repeatedVisible F u e).1
    (repaired F (fun t => (e t).1) j)

end
end LargeIndependentSets.LCInput

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Supported2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators Classical
open BooleanJunta PhaseTest Coefficient

lemma LayerLaw.sum_supported {r s : ℕ} (μ : LayerLaw r s) (f : Finset (Fin r) → ℚ) :
    (∑ B : {B : Finset (Fin r) // B.card = s}, μ.weight B.val * f B.val) =
      ∑ B, μ.weight B * f B := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun B : Finset (Fin r) => B.card = s))
    (by simp) (fun B => μ.weight B * f B)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : B.card = s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, μ.support B h, zero_mul]

noncomputable def LayerLaw.supported {r s : ℕ} (μ : LayerLaw r s) :
    RationalLaw {B : Finset (Fin r) // B.card = s} where
  weight B := μ.weight B.val
  nonneg B := μ.nonneg B.val
  total := by
    simpa using (μ.sum_supported (fun _ => 1)).trans (by simpa using μ.total)

noncomputable def samplerLaw {L R : Type} [Fintype L] [Fintype R]
    {n s : ℕ} (μ : LayerLaw (n+1) s) (m k : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ) :
    RationalLaw (SamplerOutcome L R n s m k) :=
  μ.supported.bind (fun B =>
    (RationalLaw.pi (fun _ : B.val => Coefficient.law m hρ)).bind (fun _ =>
      RationalLaw.uniform (SubchainCoord L R n B.val → Cube k)))

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SamplerParameters
attribute [-instance] _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators
open MeasureTheory PhaseTest

namespace SamplerParameters

noncomputable abbrev law (p : SamplerParameters) (L R : Type) [Fintype L] [Fintype R] :=
  samplerLaw (L:=L) (R:=R) p.μ p.m p.k p.hρ

abbrev Vertices (p : SamplerParameters) (L R C : Type) [Fintype L] [Fintype R] :=
  (p.law L R).Vertices C p.n

noncomputable def location (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (v : p.Vertices L R C) :=
  sampleLocation lc v.1 p.hs v.2.1

noncomputable def graph (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) : SimpleGraph (p.Vertices L R C) :=
  gridGraph (layeredSystem lc p.n) p.even (p.location lc)

end SamplerParameters

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Simple
attribute [-instance] _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

namespace SamplerParameters

def CliqueTest (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) : Prop :=
  ∃ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
    pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)

end SamplerParameters

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Capped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ShortestPaths

namespace Capped

instance instMin (B : ℕ) : Min (Capped B) := ⟨fun a b => if a.val ≤ b.val then a else b⟩
instance instAdd (B : ℕ) : Add (Capped B) := ⟨fun a b => ⟨min (a.val+b.val) (B+1),min_le_right _ _⟩⟩

lemma min_val {B : ℕ} (a b : Capped B) : (min a b).val = min a.val b.val := by
  change (if a.val ≤ b.val then a else b).val = _
  split <;> simp_all [le_of_not_ge]

lemma add_val {B : ℕ} (a b : Capped B) : (a+b).val = min (a.val+b.val) (B+1) := rfl

end Capped
end LargeIndependentSets.ShortestPaths

namespace LargeIndependentSets.ShortestPaths.Capped

def Matrix.pivot {B n : ℕ} (a : Matrix B n) (k : Fin n) : Matrix B n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => ShortestPaths.pivot a.get k i j))

def Matrix.run {B n : ℕ} (a : Matrix B n) : List (Fin n) → Matrix B n
  | [] => a
  | k::ks => (a.pivot k).run ks

def Matrix.allPairs {B n : ℕ} (a : Matrix B n) : Matrix B n := a.run (List.finRange n)

def Matrix.ofInteger (B : ℕ) {n : ℕ} (a : ShortestPaths.Matrix n) : Matrix B n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => clip B (a.get i j)))

end LargeIndependentSets.ShortestPaths.Capped

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineFixedBlockMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

end IndependentSetsGames.Foundations.Complexity.MachineFixedBlockMap

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineInitialHeaders
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineInitialHeaders

open Turing
open Reduction.MachineTransfer
open Reduction.MachineSubstitution
open MachineCopy

variable {K Λ σ : Type} [DecidableEq K]

theorem prefixScanTrace (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (base : K → List Bool) (n : ℕ) (suffix saved emitted : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        forkTapes source scratch output base (encodeWord n ++ suffix) saved emitted⟩) =
      some ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix)
          (List.replicate n true ++ saved) (List.replicate (scale * n) true ++ emitted)⟩ := by
  induction n generalizing saved emitted register with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
      Nat.mul_zero]
    change some (TM2.stepAux (program again) _ _) = _
    rw [atScan, prefixStep_false source scratch output hst hso hto]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some (TM2.stepAux (program again) _ _)) = _
    rw [atScan]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    rw [prefixStep_true source scratch output hst hso hto]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, some true),
        forkTapes source scratch output base (encodeWord n ++ suffix)
          (true :: saved) (List.replicate scale true ++ emitted)⟩) = _
    rw [ih]
    have hs : List.replicate n true ++ true :: saved =
        true :: (List.replicate n true ++ saved) := by
      rw [replicate_append_cons, List.replicate_succ, List.cons_append]
    simp only [hs, Nat.mul_succ, List.replicate_add, List.append_assoc]

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
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _ first second)
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

end IndependentSetsGames.Foundations.Complexity.MachineInitialHeaders

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineRow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open IndependentSetsGames.Foundations.PCP

theorem encodeBits_graphWords (bits : List Bool) :
    encodeBits bits = encodeWords (bits.map GraphTables.bitWord) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [encodeBits, encodeBit, encodeWords,
      GraphTables.bitWord, encodeWord, ih]

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_RawInitialMachineStart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

def firstTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => encodeWord m ++ clauseBits
  | .«variables» => encodeWord n
  | _ => []

def counterTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | _ => []

def headerTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

def startTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .index => [false]
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

end IndependentSetsGames.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_RawInitialMachineLoopData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def loopTapes (n i remaining : Nat) (input reversed : List Bool) : Tape → List Bool
  | .input => input
  | .«variables» => encodeWord n
  | .counter => encodeWord remaining
  | .index => encodeWord i
  | .reversed => reversed
  | _ => []

end IndependentSetsGames.Foundations.PCP.RawInitialMachineLoopData
namespace IndependentSetsGames.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem bitWord_head (b : Bool) :
    (encodeWord (if b then 1 else 0)).head? = some b := by
  cases b <;> rfl

end IndependentSetsGames.Foundations.PCP.RawInitialMachinePhases

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_RawInitialMachineRows
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

theorem reverse_encodeWord_add (a b : ℕ) :
    (encodeWord b).reverse ++ List.replicate a true = (encodeWord (a + b)).reverse := by
  simp only [encodeWord, List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [Nat.add_comm a b, List.replicate_add]
  simp only [List.append_assoc]

end IndependentSetsGames.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_RawInitialMachineFinish
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

def finishTapes (n m : Nat) (rev : List Bool) : Tape → List Bool :=
  tapes (encodeWord n) [false] (encodeWord m) rev []

theorem update_finish (n m : Nat) (rev word : List Bool) :
    Function.update (finishTapes n m rev) .reversed word = finishTapes n m word :=
  update_reversed _ _ _ _ _ _

end IndependentSetsGames.Foundations.PCP.RawInitialMachineFinish

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineUnaryEqualityBit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

def bitEncoding (bit : Bool) : List Bool := encodeWord (if bit then 1 else 0)

theorem encodeWord_eq_iff (a b : Nat) : encodeWord a = encodeWord b ↔ a = b := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    simp only [encodeWord_length] at hlength
    omega
  · rintro rfl
    rfl

theorem emit_step (destination : K) (bit : Bool) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (label : Λ) (atEmit : program label = emit destination bit exit)
    (state : State A) (base : K → List Bool) :
    TM2.step program ⟨some label, state, base⟩ =
      some ⟨exit, state,
        Function.update base destination (bitEncoding bit ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) state base) = _
  rw [atEmit]
  cases bit <;> cases exit <;>
    simp [emit, exitAt, TM2.stepAux, bitEncoding, encodeWord, Function.update_idem]

end IndependentSetsGames.Foundations.Complexity.MachineUnaryEqualityBit

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def shift (t : Nat) : Tape t → Tape (t + 1) := Sum.map id Fin.succ

theorem shift_injective (t : Nat) : Function.Injective (shift t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [shift]

def rotorRole (t : Nat) (i : Fin 7) : Tape (t + 1) :=
  if i = 0 then .inl 0 else if i = 1 then .inr (first (t + 1)) else
  if i = 2 then .inl 1 else if i = 3 then .inl 2 else
  if i = 4 then .inl 3 else if i = 5 then .inr (first t).succ else .inl 4

theorem rotorRole_injective (t : Nat) : Function.Injective (rotorRole t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rotorRole, first, Fin.ext_iff]

end IndependentSetsGames.Foundations.Complexity.PoweringMachineWord

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineTapes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineTapes

theorem wordSharedRole_injective (target : Bool) : Function.Injective (wordSharedRole target) := by
  cases target <;> decide

theorem wordSharedRole_ne_start (target : Bool) :
    ∀ i : Fin 6, wordSharedRole target i ≠ 1 := by
  cases target <;> decide

theorem trajectoryPlacement_injective {t max : Nat} (ht : t ≤ max) :
    Function.Injective (trajectoryPlacement ht) := by
  intro a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro _
      rfl
    · intro h
      change (Sum.inl (1 : Fin 11) : Tape max) = .inr (Fin.castLE ht j) at h
      cases h
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inl (1 : Fin 11) at h
      cases h
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inr (Fin.castLE ht j) at h
      have hc : Fin.castLE ht i = Fin.castLE ht j := Sum.inr.inj h
      have hv : i.val = j.val := congrArg (fun x : Fin max => x.val) hc
      have hij : i = j := Fin.ext hv
      exact congrArg Fin.succ hij

theorem wordShared_ne_trajectory {t max : Nat} (ht : t ≤ max) (target : Bool)
    (i : Fin 6) :
    ∀ j : Fin (t + 1),
      (Sum.inl (wordSharedRole target i) : Tape max) ≠ trajectoryPlacement ht j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inl (1 : Fin 11) at h
    exact wordSharedRole_ne_start target i (Sum.inl.inj h)
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inr (Fin.castLE ht k) at h
    cases h

theorem wordPlacement_injective {t max : Nat} (ht : t ≤ max) (target : Bool) :
    Function.Injective (wordPlacement ht target) := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact congrArg Sum.inl (wordSharedRole_injective target (Sum.inl.inj h))
      | inr j =>
          exact False.elim (wordShared_ne_trajectory ht target i j h)
  | inr i =>
      cases b with
      | inl j =>
          exact False.elim (wordShared_ne_trajectory ht target j i h.symm)
      | inr j =>
          exact congrArg Sum.inr (trajectoryPlacement_injective ht h)

theorem relationPlacement_injective (max : Nat) : Function.Injective (relationPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [relationPlacement]

theorem equalityPlacement_injective (max : Nat) : Function.Injective (equalityPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [equalityPlacement]

end IndependentSetsGames.Foundations.Complexity.PoweringMachineTapes

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineEqualityField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev Tape := PoweringMachineTapes.Tape

end IndependentSetsGames.Foundations.Complexity.PoweringMachineEqualityField

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineLoop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop

open Turing

instance instFintypeHeaderTape : Fintype HeaderTape where
  elems := {.source, .counter, .vertices, .darts}
  complete value := by cases value <;> simp

abbrev HeaderAlphabet (_ : HeaderTape) := Bool

def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize_ =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

def scanConfiguration {σ : Type} (B remaining processed : Nat)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨some .scan, (ambient, register), scanTapes B remaining processed suffix⟩

def finalConfiguration {σ : Type} (B n : Nat) (suffix : List Bool) (ambient : σ) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨none, (ambient, none), finalTapes B n suffix⟩

theorem initializeStep {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩ =
        some (scanConfiguration B n 0 suffix ambient none) := by
  simp only [TM2.step, headerProgram, TM2.stepAux]
  congr 2
  funext tape
  cases tape <;> simp [initialTapes, scanTapes, encodeWord]

theorem scanStep_zero {σ : Type} (B processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B) (scanConfiguration B 0 processed suffix ambient register) =
      some (finalConfiguration B processed suffix ambient) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext tape
  cases tape <;> simp [finalTapes, scanTapes]

theorem scanStep_succ {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      (scanConfiguration B (remaining + 1) processed suffix ambient register) =
      some (scanConfiguration B remaining (processed + 1) suffix ambient none) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_succ, List.cons_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]
  rw [stepAux_pushTrue]
  simp only [TM2.stepAux]
  congr 2
  funext tape
  cases tape <;>
    simp [scanTapes, encodeWord, Nat.mul_add, List.replicate_add,
      List.replicate_succ, List.append_assoc, Nat.add_comm,
      -List.replicate_append_replicate]

theorem scanTrace {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (some (scanConfiguration B remaining processed suffix ambient register)) =
      some (finalConfiguration B (processed + remaining) suffix ambient) := by
  induction remaining generalizing processed register with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      scanStep_zero B processed suffix ambient register
  | succ remaining ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (TM2.step (headerProgram B)
        (scanConfiguration B (remaining + 1) processed suffix ambient register)) = _
    rw [scanStep_succ, ih]
    simp only [Nat.add_comm, Nat.add_left_comm]

theorem headerTrace {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 2]
      (some ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩) =
      some (finalConfiguration B n suffix ambient) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 1]
    (TM2.step (headerProgram B)
      ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩) = _
  rw [initializeStep]
  simpa only [Nat.zero_add] using scanTrace B n 0 suffix ambient none

end IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineInitialize
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop

def finalOutput (max : Nat) : GlobalTape max := .inr (.inr ())

theorem commonPlacement_injective (max : Nat) : Function.Injective (commonPlacement max) := by
  intro a b h
  by_cases ha : a = PoweringMachineTapes.start max <;>
    by_cases hb : b = PoweringMachineTapes.start max <;>
      simp_all [commonPlacement]

theorem commonPlacement_ne_finalOutput (max : Nat) (tape : PoweringMachineTapes.Tape max) :
    commonPlacement max tape ≠ finalOutput max := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, finalOutput, h]

theorem commonPlacement_ne_header (max : Nat) (tape : PoweringMachineTapes.Tape max)
    (field : HeaderTape) (hne : field ≠ .counter) :
    commonPlacement max tape ≠ .inl field := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, h, Ne.symm hne]

theorem boolAlphabet_eq (max : Nat) :
    MachineEmbedding.Alphabet HeaderAlphabet (fun _ : ExtraTape max => Bool) =
      (fun _ : GlobalTape max => Bool) := by
  funext tape
  cases tape <;> rfl

theorem castTapes_embedding {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    castTapes (boolAlphabet_eq max) (MachineEmbedding.tapes header extra) =
      mergeTapes header extra := by
  funext tape
  rw [castTapes_apply]
  cases tape <;> rfl

def initialGlobalTapes {max : Nat} (extra : ExtraTape max → List Bool) :
    GlobalTape max → List Bool := mergeTapes (fun _ => []) extra

@[simp] theorem final_extra (max B vertices : Nat) (extra : ExtraTape max → List Bool)
    (tape : ExtraTape max) :
    mergeTapes (finalTapes B vertices []) extra (.inr tape) = extra tape := rfl

end IndependentSetsGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringGlobalEnumeration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def headerTapeEquiv : HeaderTape ≃ Fin 4 where
  toFun
    | .source => 0
    | .counter => 1
    | .vertices => 2
    | .darts => 3
  invFun i := if i = 0 then .source else if i = 1 then .counter
    else if i = 2 then .vertices else .darts
  left_inv tape := by cases tape <;> rfl
  right_inv i := by fin_cases i <;> rfl

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

def extraTapeEquiv (max : Nat) : ExtraTape max ≃ Fin (11 + max + 1) :=
  (Equiv.sumCongr (sharedTapeEquiv max) unitTapeEquiv).trans finSumFinEquiv

def globalTapeEquiv (max : Nat) : GlobalTape max ≃ Fin (4 + (11 + max + 1)) :=
  (Equiv.sumCongr headerTapeEquiv (extraTapeEquiv max)).trans finSumFinEquiv

def enumeration (max : Nat) : Fin (4 + (11 + max + 1)) ≃ GlobalTape max :=
  (globalTapeEquiv max).symm

@[simp] theorem globalTapeEquiv_enumeration (max : Nat) (i : Fin (4 + (11 + max + 1))) :
    globalTapeEquiv max (enumeration max i) = i :=
  (globalTapeEquiv max).apply_symm_apply i

@[simp] theorem enumeration_globalTapeEquiv (max : Nat) (tape : GlobalTape max) :
    enumeration max (globalTapeEquiv max tape) = tape :=
  (globalTapeEquiv max).symm_apply_apply tape

@[simp] theorem source_index (max : Nat) :
    (globalTapeEquiv max (.inl .source)).val = 0 := rfl

@[simp] theorem counter_index (max : Nat) :
    (globalTapeEquiv max (.inl .counter)).val = 1 := rfl

@[simp] theorem vertices_index (max : Nat) :
    (globalTapeEquiv max (.inl .vertices)).val = 2 := rfl

@[simp] theorem darts_index (max : Nat) :
    (globalTapeEquiv max (.inl .darts)).val = 3 := rfl

@[simp] theorem finalOutput_index (max : Nat) :
    (globalTapeEquiv max (finalOutput max)).val = 4 + (11 + max) := rfl

end IndependentSetsGames.Foundations.Complexity.PoweringGlobalEnumeration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineRelationField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

def lookupTapes (placement : PoweringMachineTapes.Tape max → K) (i : Fin 5) : K :=
  placement (PoweringMachineTapes.relationPlacement max i.succ)

omit [DecidableEq K] in
theorem lookupTapes_injective (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) : Function.Injective (lookupTapes placement) := by
  intro i j h
  exact (Fin.succ_injective _) ((PoweringMachineTapes.relationPlacement_injective max) (distinct h))

omit [DecidableEq K] in
theorem source_outside_lookup (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) :
    ∀ i, placement (.inl 6) ≠ lookupTapes placement i := by
  intro i h
  have heq : PoweringMachineTapes.relationPlacement max 0 = PoweringMachineTapes.relationPlacement max i.succ := by
    simpa [PoweringMachineTapes.leftEndpoint] using distinct h
  have hi := (PoweringMachineTapes.relationPlacement_injective max) heq
  have hv := congrArg Fin.val hi
  simp at hv

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRelationField

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev Tape := PoweringMachineTapes.Tape

end IndependentSetsGames.Foundations.Complexity.PoweringMachineField

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_StoredFloyd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.StoredFloyd
open ShortestPaths
open IndependentSetsCut.CounterMachine

def State.step {B : ℕ} (s : State B) : State B where
  n := s.n
  k := s.k+1
  matrix := if h : s.k < s.n then s.matrix.pivot ⟨s.k,h⟩ else s.matrix

lemma read_cell {B : ℕ} (s : State B) (i j : Fin s.n) :
    Expr.wordValue s.bits (2+i.val*s.n+j.val) = (s.matrix.get i j).val := by
  have hn : 0 < s.n := Nat.zero_lt_of_lt i.isLt
  have hlt : i.val*s.n+j.val < s.n*s.n := by
    calc
      _ < (i.val+1)*s.n := by nlinarith [j.isLt]
      _ ≤ s.n*s.n := Nat.mul_le_mul_right _ i.isLt
  rw [State.bits,IndependentSetsCut.CounterMachine.UnaryTables.wordValue_words _ _ _ (by omega)]
  simp only [State.value,show 2+i.val*s.n+j.val≠0 by omega,ite_false,
    show 2+i.val*s.n+j.val≠1 by omega]
  rw [show 2+i.val*s.n+j.val-2=i.val*s.n+j.val by omega]
  have hd : (i.val*s.n+j.val)/s.n=i.val := by
    rw [Nat.mul_comm i.val s.n,Nat.mul_add_div hn,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  simp [hd, Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

def rowExpr : Expr := Expr.quotient (.sub (.arg 0) (.const 2)) sizeExpr
def colExpr : Expr := Expr.remainder (.sub (.arg 0) (.const 2)) sizeExpr

def valueExpr (B : ℕ) : Expr :=
  Expr.cond (Expr.equal (.arg 0) (.const 0)) sizeExpr
    (Expr.cond (Expr.equal (.arg 0) (.const 1)) (.add pivotExpr (.const 1))
      (Expr.cond (Expr.lt pivotExpr sizeExpr)
        (minExpr (cellExpr rowExpr colExpr)
          (minExpr (.add (cellExpr rowExpr pivotExpr) (cellExpr pivotExpr colExpr)) (.const (B+1))))
        (cellExpr rowExpr colExpr)))

end LargeIndependentSets.StoredFloyd

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FiniteScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.FiniteScan
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open Turing
open scoped BigOperators

def State.value {m : ℕ} (s : State m) (w : ℕ) : ℕ :=
  if w=0 then s.input.length else if w=1 then s.k else
    if w<2+s.input.length then Expr.bitValue s.input (w-2)
    else (s.history (w-(2+s.input.length))).val

def State.bits {m : ℕ} (s : State m) : List Bool :=
  UnaryTables.words s.value (3+2*s.input.length)

@[simp] lemma read_n {m : ℕ} (s : State m) : Expr.wordValue s.bits 0 = s.input.length := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]
@[simp] lemma read_k {m : ℕ} (s : State m) : Expr.wordValue s.bits 1 = s.k := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]

lemma read_input {m : ℕ} (s : State m) (i : ℕ) (hi : i < s.input.length) :
    Expr.wordValue s.bits (2+i) = Expr.bitValue s.input i := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value,show 2+i≠1 by omega,show 2+i<2+s.input.length by omega]

lemma read_history {m : ℕ} (s : State m) (i : ℕ) (hi : i ≤ s.input.length) :
    Expr.wordValue s.bits (2+s.input.length+i) = (s.history i).val := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value,
    show 2+s.input.length+i≠1 by omega,show ¬2+s.input.length+i<2+s.input.length by omega]

def nExpr : Expr := .word (.const 0)
def kExpr : Expr := .word (.const 1)
def inputExpr (i : Expr) : Expr := .word (.add (.const 2) i)
def historyExpr (i : Expr) : Expr := .word (.add (.add (.const 2) nExpr) i)

def transitionExpr {m : ℕ} (δ : Fin m → Bool → Fin m) (q b : Expr) : Expr :=
  Expr.listSum (List.finRange m) (fun i => .mul (Expr.equal q (.const i.val))
    (Expr.cond b (.const (δ i true).val) (.const (δ i false).val)))

lemma transitionExpr_eval {m : ℕ} (δ : Fin m → Bool → Fin m) (q b : Expr)
    (s : List Bool) (args : ℕ → ℕ) (i : Fin m) (c : Bool)
    (hq : q.eval s args=i.val) (hb : b.eval s args=if c then 1 else 0) :
    (transitionExpr δ q b).eval s args = (δ i c).val := by
  simp only [transitionExpr,Expr.listSum_eval,Expr.eval,Expr.equal_eval,Expr.cond_eval,hq,hb]
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false,
    one_ne_zero, not_false_eq_true]
  all_goals
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simp [Fin.val_inj]

@[simp] lemma nExpr_eval {m : ℕ} (s : State m) (args : ℕ → ℕ) :
    nExpr.eval s.bits args = s.input.length := by simp [nExpr,Expr.eval]
@[simp] lemma kExpr_eval {m : ℕ} (s : State m) (args : ℕ → ℕ) :
    kExpr.eval s.bits args = s.k := by simp [kExpr,Expr.eval]

@[simp] lemma inputExpr_eval (i : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (inputExpr i).eval s args = Expr.wordValue s (2+i.eval s args) := by simp [inputExpr,Expr.eval]
@[simp] lemma historyExpr_eval (i : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (historyExpr i).eval s args = Expr.wordValue s (2+nExpr.eval s args+i.eval s args) := by
  simp [historyExpr,Expr.eval]

def countExpr : Expr := .add (.const 3) (.mul (.const 2) nExpr)
def valueExpr {m : ℕ} (δ : Fin m → Bool → Fin m) : Expr :=
  Expr.cond (Expr.equal (.arg 0) (.const 1)) (.add kExpr (.const 1))
    (Expr.cond (.mul (Expr.lt kExpr nExpr)
      (Expr.equal (.arg 0) (.add (.add (.const 3) nExpr) kExpr)))
      (transitionExpr δ (historyExpr kExpr) (inputExpr kExpr)) (.word (.arg 0)))

lemma valueExpr_eval {m : ℕ} (δ : Fin m → Bool → Fin m) (s : State m)
    (w : ℕ) (hw : w<3+2*s.input.length) :
    (valueExpr δ).eval s.bits (fun _ => w) = (step δ s).value w := by
  have old := UnaryTables.wordValue_words s.value (3+2*s.input.length) w hw
  change Expr.wordValue s.bits w = s.value w at old
  by_cases hw1 : w=1
  · subst w
    simp [valueExpr,Expr.eval,State.value,step]
  by_cases hk : s.k < s.input.length
  · have ht : (transitionExpr δ (historyExpr kExpr) (inputExpr kExpr)).eval s.bits (fun _ => w) =
        (δ (s.history s.k) s.input[s.k]).val := by
      apply transitionExpr_eval
      · simp [read_history s s.k hk.le]
      · simp [read_input s s.k hk,Expr.bitValue,List.getElem?_eq_getElem hk]
    simp only [valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,hw1,ite_false,
      ne_eq,not_true_eq_false,ite_true,nExpr_eval,kExpr_eval,Expr.lt_eval,Expr.word_eval,
      hk,one_mul,ht,old]
    simp only [step,dite_eq_left hk,State.value]
    by_cases hw0 : w=0
    · subst w; simp [show ¬0=3+s.input.length+s.k by omega]
    by_cases hwl : w<2+s.input.length
    · have hne : w≠3+s.input.length+s.k := by omega
      simp [hw0,hw1,hwl,hne]
    · have he : w=3+s.input.length+s.k ↔ w-(2+s.input.length)=s.k+1 := by omega
      simp only [hw0,hw1,hwl,ite_false,Function.update_apply]
      by_cases hwe : w=3+s.input.length+s.k
      · rw [ite_eq_left hwe,ite_eq_left (he.mp hwe)]; simp
      · rw [ite_eq_right hwe,ite_eq_right (mt he.mpr hwe)]; simp
  · simp [valueExpr,Expr.eval,hk,hw1,old,step,State.value]

lemma body_spec {m : ℕ} (δ : Fin m → Bool → Fin m) (s : State m) :
    UnaryTables.words (fun j => (valueExpr δ).eval s.bits (fun _ => j))
      (countExpr.eval s.bits (fun _ => 0)) = (step δ s).bits := by
  have hn : countExpr.eval s.bits (fun _ => 0) = 3+2*s.input.length := by
    simp [countExpr,Expr.eval]
  rw [hn]
  exact UnaryTables.words_congr (valueExpr_eval δ s)

noncomputable def body {m : ℕ} (δ : Fin m → Bool → Fin m) :
    TM2ComputableInPolyTime State.bits State.bits (step δ) :=
  UnaryTables.encodedComputer State.bits State.bits (step δ) countExpr (valueExpr δ) (body_spec δ)

lemma iterate_input {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool) (i : ℕ) :
    ((step δ)^[i] (initial q s)).input = s := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [Function.iterate_succ_apply',step] using ih

lemma iterate_k {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool) (i : ℕ) :
    ((step δ)^[i] (initial q s)).k = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [Function.iterate_succ_apply',step,ih]

lemma history_prefix {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool)
    (i : ℕ) (hi : i ≤ s.length) (j : ℕ) (hj : j ≤ i) :
    ((step δ)^[i] (initial q s)).history j = (s.take j).foldl δ q := by
  induction i generalizing j with
  | zero =>
    have : j=0 := by omega
    subst j
    rfl
  | succ i ih =>
    have hk : i < s.length := hi
    rw [Function.iterate_succ_apply']
    simp only [step,iterate_k,iterate_input,dite_eq_left hk,Function.update_apply]
    by_cases he : j=i+1
    · rw [ite_eq_left he]
      subst j
      rw [ih hk.le i le_rfl,List.take_succ_eq_append_getElem hk,List.foldl_append]
      rfl
    · rw [ite_eq_right he]
      exact ih hk.le j (by omega)

def output {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool) : State m :=
  (step δ)^[s.length] (initial q s)

lemma output_history {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool)
    (j : ℕ) (hj : j ≤ s.length) :
    (output δ q s).history j = (s.take j).foldl δ q := history_prefix δ q s _ le_rfl j hj

lemma value_le {m : ℕ} (s : State m) (w : ℕ) : s.value w ≤ s.input.length+s.k+m+1 := by
  unfold State.value
  split
  · omega
  · split
    · omega
    · split
      · unfold Expr.bitValue; split <;> omega
      · have := (s.history (w-(2+s.input.length))).isLt; omega

lemma bits_length_le {m : ℕ} (s : State m) :
    s.bits.length ≤ (3+2*s.input.length)*(s.input.length+s.k+m+2) := by
  rw [State.bits,UnaryTables.words_length]
  unfold UnaryTables.offset
  calc
    _ ≤ ∑ _ ∈ Finset.range (3+2*s.input.length), (s.input.length+s.k+m+2) := by
      apply Finset.sum_le_sum
      intro w _hw
      have := value_le s w
      omega
    _ = _ := by simp

def countedInput {m : ℕ} (q : Fin m) (s : List Bool) : List Bool :=
  BoundedIteration.counted List.length State.bits (initial q) s

lemma intermediate_bound {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool)
    (i : ℕ) (hi : i ≤ s.length) :
    ((step δ)^[i] (initial q s)).bits.length ≤ (lengthPolynomial m).eval (countedInput q s).length := by
  rw [lengthPolynomial_eval]
  apply (bits_length_le _).trans
  rw [iterate_input,iterate_k]
  have hn : s.length ≤ (countedInput q s).length :=
    BoundedIteration.count_le List.length State.bits (initial q) s
  gcongr; omega

noncomputable def countedCertificate {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) :
    TM2ComputableInPolyTime (countedInput q) State.bits (output δ q) :=
  BoundedIteration.certificate State.bits (step δ) (initial q) List.length (body δ)
    (lengthPolynomial m) (intermediate_bound δ q)

lemma words_cons (f : ℕ → ℕ) (n : ℕ) :
    UnaryTables.words f (n+1) = (List.replicate (f 0) true ++ [false]) ++
      UnaryTables.words (fun j => f (j+1)) n := by
  simp [UnaryTables.words,List.range_succ_eq_map,List.flatMap_map,Function.comp_def]

def initialCount : Expr := .add (.const 4) (.mul (.const 2) .length)
def initialValue {m : ℕ} (q : Fin m) : Expr :=
  Expr.cond (Expr.le (.arg 0) (.const 1)) .length
    (Expr.cond (Expr.equal (.arg 0) (.const 2)) (.const 0)
      (Expr.cond (Expr.lt (.arg 0) (.add (.const 3) .length))
        (.bit (.sub (.arg 0) (.const 3))) (.const q.val)))

lemma initialValue_zero {m : ℕ} (q : Fin m) (s : List Bool) :
    (initialValue q).eval s (fun _ => 0) = s.length := by simp [initialValue,Expr.eval]

lemma initialValue_succ {m : ℕ} (q : Fin m) (s : List Bool) (w : ℕ) :
    (initialValue q).eval s (fun _ => w+1) = (initial q s).value w := by
  simp only [initialValue,Expr.cond_eval,Expr.le_eval,Expr.equal_eval,Expr.lt_eval,Expr.eval]
  have h1 : w+1≤1 ↔ w=0 := by omega
  have h2 : w+1=2 ↔ w=1 := by omega
  have h3 : w+1<3+s.length ↔ w<2+s.length := by omega
  simp only [h1,h2,h3]
  by_cases hw0 : w=0
  · simp [hw0,initial,State.value]
  by_cases hw1 : w=1
  · simp [hw1,initial,State.value]
  have ht : w+1-3=w-2 := by omega
  simp [hw0,hw1,ht,initial,State.value,Expr.bitValue]
  rfl

end LargeIndependentSets.FiniteScan

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryNameTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinaryNames
open IndependentSetsCut.CounterMachine
open scoped BigOperators

lemma frame_eq (s : List Bool) : LargeIndependentSets.frame s = IndependentSetsCut.CounterMachine.frame s := by
  induction s with
  | nil => rfl
  | cons b s ih => simp only [LargeIndependentSets.frame,IndependentSetsCut.CounterMachine.frame,ih]

def rawExpr (i : Expr) : Expr :=
  Expr.cond (Expr.lt i FiniteScan.nExpr) (FiniteScan.inputExpr i) (.const 0)

lemma rawExpr_eval {m : ℕ} (s : FiniteScan.State m) (i : Expr) (a : ℕ → ℕ) :
    (rawExpr i).eval s.bits a = if raw s.input (i.eval s.bits a) then 1 else 0 := by
  by_cases hi : i.eval s.bits a < s.input.length
  · simp [rawExpr,hi,FiniteScan.read_input s _ hi,Expr.bitValue,raw]
  · simp [rawExpr,Expr.eval,hi,raw_out s.input (i.eval s.bits a) (by omega)]

def nameLengthExpr (p : Expr) : Expr := Expr.least (.add FiniteScan.nExpr (.const 1))
  (.zero (rawExpr (.add (.add (p.rename Nat.succ) (.const 1)) (.mul (.const 2) (.arg 0)))))

lemma nameLengthExpr_eval {m : ℕ} (s : FiniteScan.State m) (p : Expr) (a : ℕ → ℕ) :
    (nameLengthExpr p).eval s.bits a = nameLength s.input (p.eval s.bits a) := by
  unfold nameLengthExpr
  apply Expr.least_eq
  · simpa [Expr.eval] using Nat.lt_succ_of_le (nameLength_le s.input _)
  · simp [Expr.eval,rawExpr_eval,Expr.bind,nameLength_end]
  · intro j hj
    simp [Expr.eval,rawExpr_eval,Expr.bind,nameLength_before s.input _ j hj]

def payloadEqExpr (p q : Expr) : Expr := .mul (Expr.equal (nameLengthExpr p) (nameLengthExpr q))
  (.zero (.sum (nameLengthExpr p) (.zero (Expr.equal
    (rawExpr (.add (.add (p.rename Nat.succ) (.const 2)) (.mul (.const 2) (.arg 0))))
    (rawExpr (.add (.add (q.rename Nat.succ) (.const 2)) (.mul (.const 2) (.arg 0))))))))

lemma payloadEqExpr_eval {m : ℕ} (s : FiniteScan.State m) (p q : Expr) (a : ℕ → ℕ) :
    (payloadEqExpr p q).eval s.bits a =
      if payload s.input (p.eval s.bits a) = payload s.input (q.eval s.bits a) then 1 else 0 := by
  have hb (x y : Bool) : ((if x then 1 else 0 : ℕ) = if y then 1 else 0) ↔ x=y := by
    cases x <;> cases y <;> decide
  simp only [payloadEqExpr,Expr.eval,Expr.equal_eval,nameLengthExpr_eval,rawExpr_eval,
    Expr.rename_eval,Expr.bind,hb]
  have hz : (∑ j ∈ Finset.range (nameLength s.input (p.eval s.bits a)),
      if raw s.input (p.eval s.bits a+2+2*j)=raw s.input (q.eval s.bits a+2+2*j) then 0 else 1)=0 ↔
      ∀ j<nameLength s.input (p.eval s.bits a),
        raw s.input (p.eval s.bits a+2+2*j)=raw s.input (q.eval s.bits a+2+2*j) := by
    simp [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [show ∀ b : Prop, ∀ _ : Decidable b, (if (if b then (1:ℕ) else 0)=0 then 1 else 0) =
      if b then 0 else 1 by intros; split_ifs <;> simp_all]
  simp only [hz,payload_eq_iff]
  by_cases h : nameLength s.input (p.eval s.bits a)=nameLength s.input (q.eval s.bits a)
  · simp [h]
  · simp [h]

def minExpr (a b : Expr) : Expr := Expr.cond (Expr.le a b) a b
@[simp] lemma minExpr_eval (x y : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (minExpr x y).eval s a = min (x.eval s a) (y.eval s a) := by
  by_cases h : x.eval s a ≤ y.eval s a <;> simp [minExpr,h, min_def]

def keyExpr (p : Expr) : Expr := Expr.least (.add FiniteScan.nExpr (.const 1))
  (payloadEqExpr (.arg 0) ((minExpr p FiniteScan.nExpr).rename Nat.succ))

lemma keyExpr_eval {m : ℕ} (s : FiniteScan.State m) (p : Expr) (a : ℕ → ℕ) :
    (keyExpr p).eval s.bits a = key s.input (p.eval s.bits a) := by
  unfold keyExpr
  apply Expr.least_eq
  · simpa [Expr.eval] using Nat.lt_succ_of_le (key_le s.input _)
  · simp only [payloadEqExpr_eval,Expr.eval,Expr.bind,Expr.rename_eval,minExpr_eval,FiniteScan.nExpr_eval]
    have hk : payload s.input (key s.input (p.eval s.bits a)) =
        payload s.input (min (p.eval s.bits a) s.input.length) :=
      (Nat.find_spec (key_exists s.input (p.eval s.bits a))).2
    simpa only [hk,ite_true] using (show (1:ℕ)≠0 by decide)
  · intro j hj
    have hjn : j ≤ s.input.length := (Nat.le_of_lt hj).trans (key_le s.input _)
    have hne : payload s.input j ≠ payload s.input (min (p.eval s.bits a) s.input.length) := by
      intro he
      exact Nat.find_min (key_exists s.input (p.eval s.bits a)) hj ⟨hjn,he⟩
    simp [payloadEqExpr_eval,Expr.eval,Expr.bind,hne]

def nextExpr (p : Expr) : Expr := .add (.add p (.const 2)) (.mul (.const 2) (nameLengthExpr p))
lemma nextExpr_eval {m : ℕ} (s : FiniteScan.State m) (p : Expr) (a : ℕ → ℕ) :
    (nextExpr p).eval s.bits a = next s.input (p.eval s.bits a) := by
  simp [nextExpr,Expr.eval,nameLengthExpr_eval,next]

end LargeIndependentSets.BinaryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinarySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinarySyntax

noncomputable def annotated (s : List Bool) :=
  FiniteScan.output finiteTransition (phaseEquiv .headerMark) s

lemma annotated_history (s : List Bool) (j : ℕ) (hj : j ≤ s.length) :
    (annotated s).history j = phaseEquiv (run .headerMark (s.take j)) := by
  rw [annotated,FiniteScan.output_history _ _ _ j hj,finite_run]

end LargeIndependentSets.BinarySyntax

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryNaming
attribute [-instance] _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LargeIndependentSets.GeometryNames

open scoped Classical

def PointStep {L R : Type} {n D : ℕ} (h : Fin n) (f : L → R)
    (a b : StaticPoint L R n D) : Prop :=
  ∃ (x : MixedTuple L R n h.val → ZMod D) (y : MixedTuple L R n (h.val+1) → ZMod D),
    a=⟨h.castSucc,x⟩ ∧ b=⟨h.succ,y⟩ ∧ x=y ∘ mixedProject h f

lemma forward_iff {U V L R C : Type} {n D : ℕ} (lc : LabelCoverData U V L R C)
    (u u' : Fin n → U) (v v' : Fin n → V) (a b : StaticPoint L R n D) :
    (layeredSystem lc n).ForwardZero D (decode u v a) (decode u' v' b) ↔
      ∃ h c, PointStep h (lc.project c) a b ∧ QuestionStep lc h c u u' v v' := by
  constructor
  · intro hz
    rw [ShortestPaths.forwardZero_iff] at hz
    obtain ⟨π,hπ,hcoord⟩ := hz
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    change LayerImposed lc n ⟨i,mixed u v i.val⟩ ⟨j,mixed u' v' j.val⟩ π at hπ
    cases hπ with
    | adjacent h q q' c hl hr ho =>
      refine ⟨h,c,?_,?_⟩
      · exact ⟨a,b,rfl,rfl,hcoord⟩
      · exact (questionStep_iff lc h c u u' v v').mpr ⟨hl,hr,ho⟩
  · rintro ⟨h,c,⟨x,y,rfl,rfl,hxy⟩,hq⟩
    rw [ShortestPaths.forwardZero_iff]
    obtain ⟨hl,hr,ho⟩ := (questionStep_iff lc h c u u' v v').mp hq
    exact ⟨mixedProject h (lc.project c),.adjacent h _ _ c hl hr ho,hxy⟩

end LargeIndependentSets.GeometryNames

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LCTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.UniformLC
open IndependentSetsCut.CounterMachine
open scoped Classical BigOperators
noncomputable section

def Table.lc {L R : Type} (t : Table L R) : LabelCoverData (Fin t.nu) (Fin t.nv) L R (Fin t.ne) :=
  ⟨t.left,t.right,t.project⟩

variable {L R : Type} [Fintype L] [Fintype R]

lemma read_field (t : Table L R) (c : Fin t.ne) (j : Fin 3) :
    Expr.wordValue t.bits (3+3*c.val+j.val) =
      if j.val=0 then (t.left c).val else if j.val=1 then (t.right c).val else projectCode (t.project c) := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by have := c.isLt; have := j.isLt; omega)]
  have hsub : 3+3*c.val+j.val-3=3*c.val+j.val := by omega
  have hdiv : (3*c.val+j.val)/3=c.val := by omega
  have hmod : (3*c.val+j.val)%3=j.val := by omega
  simp [Table.value,show 3+3*c.val+j.val≠1 by omega,
    show 3+3*c.val+j.val≠2 by omega,hsub,hdiv,hmod,c.isLt]

def fieldExpr (c : Expr) (j : ℕ) : Expr := Expr.word (.add (.add (.const 3) (.mul (.const 3) c)) (.const j))

lemma fieldExpr_eval (t : Table L R) (a : ℕ → ℕ) (c : Expr) (e : Fin t.ne)
    (hc : c.eval t.bits a=e.val) (j : Fin 3) :
    (fieldExpr c j.val).eval t.bits a =
      if j.val=0 then (t.left e).val else if j.val=1 then (t.right e).val else projectCode (t.project e) := by
  simp only [fieldExpr,Expr.word_eval,Expr.eval,hc,read_field]

end
end LargeIndependentSets.UniformLC

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_GeometryExpr
attribute [-instance] _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC
open scoped Classical BigOperators
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

abbrev size (t : Table L R) := (t.nu^n*t.nv^n)*staticCount L R n D

lemma size_pos (t : Table L R) : 0 < size L R n D t := by
  exact Nat.mul_pos (Nat.mul_pos (pow_pos t.hu _) (pow_pos t.hv _)) (staticCount_pos L R n D)

def sizeExpr : Expr := .mul (.mul (Expr.power nuExpr n) (Expr.power nvExpr n)) (.const (staticCount L R n D))
def pointExpr (x : Expr) : Expr := Expr.remainder x (.const (staticCount L R n D))
def uExpr (x : Expr) (k : Fin n) : Expr :=
  Expr.remainder (Expr.quotient
    (Expr.quotient (Expr.quotient x (.const (staticCount L R n D))) (Expr.power nvExpr n))
    (Expr.power nuExpr k.val)) nuExpr

def vExpr (x : Expr) (k : Fin n) : Expr :=
  Expr.remainder (Expr.quotient
    (Expr.remainder (Expr.quotient x (.const (staticCount L R n D))) (Expr.power nvExpr n))
    (Expr.power nvExpr k.val)) nvExpr

@[simp] lemma sizeExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    (sizeExpr L R n D).eval t.bits a=size L R n D t := by simp [sizeExpr,Expr.eval,size]

lemma uExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) (k : Fin n) :
    (uExpr L R n D x k).eval t.bits a=(((nodeEquiv L R n D t.nu t.nv).symm i).1.1 k).val := by
  simp only [uExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,nuExpr_eval,nvExpr_eval,Expr.eval,hi]
  rfl
lemma vExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) (k : Fin n) :
    (vExpr L R n D x k).eval t.bits a=(((nodeEquiv L R n D t.nu t.nv).symm i).1.2 k).val := by
  simp only [vExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,nvExpr_eval,Expr.eval,hi]
  rfl
lemma pointExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (pointExpr L R n D x).eval t.bits a=
      (Fintype.equivFin (StaticPoint L R n D) ((nodeEquiv L R n D t.nu t.nv).symm i).2).val := by
  simp only [pointExpr,Expr.remainder_eval,Expr.eval,hi]
  change _=(Fintype.equivFin _ ((Fintype.equivFin _).symm _)).val
  rw [Equiv.apply_symm_apply]
  rfl

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_TargetRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LargeIndependentSets.TargetRead
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame
open scoped Classical BigOperators

def varsExpr : Expr := Expr.word (.const 0)
def clausesExpr : Expr := Expr.word (.const 1)

end LargeIndependentSets.TargetRead

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_TargetLCExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open TargetRead TargetRepair
open scoped Classical BigOperators
noncomputable section
variable (u : ℕ)

def rankExpr (base : Expr) (f : Fin u → Expr) : Expr :=
  Expr.listSum (List.finRange u) (fun k => .mul (f k) (Expr.power base k.val))

end
end LargeIndependentSets.TargetLC

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderRowControl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

def outputPort {d : Nat} (s : Control d) : Fin (degree d) :=
  rowIndex d d (s.lastH.2,s.firstH.2)

def outputOffset {d : Nat} (s : Control d) : Fin (rowFactor d) :=
  rowIndex (cloudSize d) (degree d) (s.lastH.1,outputPort s)

def outputAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  rowFactor d * vertex + (outputOffset s).val

end IndependentSetsGames.Foundations.PCP.ExpanderRowControl

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderTableEnumeration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl
open IndependentSetsGames.Foundations.Complexity

variable {v d : Nat}

def accumulate (values : List Nat) (initial : List Bool) : List Bool :=
  values.foldl (fun accumulator value => (encodeWord value).reverse ++ accumulator) initial

theorem accumulate_append (first second : List Nat) (initial : List Bool) :
    accumulate (first ++ second) initial = accumulate second (accumulate first initial) := by
  simp only [accumulate, List.foldl_append]

end IndependentSetsGames.Foundations.PCP.ExpanderTableEnumeration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringTableLayout
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringTableLayout

open IndependentSetsGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

theorem encodeWords_flatMap {α : Type*} (items : List α)
    (words : α → List Nat) :
    encodeWords (items.flatMap words) =
      items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end IndependentSetsGames.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingPaddingWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end IndependentSetsGames.Foundations.PCP.PreprocessingPaddingWords

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingRegularWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end IndependentSetsGames.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryLink
attribute [-instance] _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open scoped Classical BigOperators
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def pointCost (a b : StaticPoint L R n D) : ℕ :=
  (Capped.clip D (copyCost (decode (fun _ => ()) (fun _ => ()) a)
    (decode (fun _ => ()) (fun _ => ()) b))).val

omit [NeZero D] in
lemma copyCost_same {U V : Type} [DecidableEq U] [DecidableEq V]
    (u u' : Fin n → U) (v v' : Fin n → V) (a b : StaticPoint L R n D) :
    (Capped.clip D (copyCost (decode u v a) (decode u' v' b))).val =
      if sameQuestion L R n D u u' v v' a b then pointCost L R n D a b else D+1 := by
  by_cases hq : sameQuestion L R n D u u' v v' a b
  · rw [ite_eq_left hq]
    have hh := (sameQuestion_iff L R n D u u' v v' a b).mp hq
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    have hij : i=j := congrArg (fun w => w.1) hh
    subst j
    have hq' : mixed u v i.val=mixed u' v' i.val :=
      eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    have hcopy (q q' : MixedTuple U V n i.val) (he : q=q') :
        copyCost (M:=LayerAnswer L R) (⟨⟨i,q⟩,a⟩ : GridLocation _ D) ⟨⟨i,q'⟩,b⟩ =
          (Finset.univ.sup (fun k => circleCost (a k) (b k)) : ℕ) := by
      subst q'
      simp [copyCost]
    rw [show copyCost (decode u v ⟨i,a⟩) (decode u' v' ⟨i,b⟩)=
      (Finset.univ.sup (fun k => circleCost (a k) (b k)) : ℕ) from hcopy _ _ hq']
    simp [pointCost,copyCost,decode]
    rfl
  · have hh := (sameQuestion_iff L R n D u u' v v' a b).not.mp hq
    simp [hq,copyCost,hh]

def questionExpr (x y c : Expr) (h : Fin n) : Expr :=
  .mul (Expr.equal (uExpr L R n D x h) (fieldExpr c 0))
    (.mul (Expr.equal (vExpr L R n D y h) (fieldExpr c 1))
      (Expr.listAll (List.finRange n) (fun k => if k=h then .const 1 else
        if k.val<h.val then Expr.equal (vExpr L R n D x k) (vExpr L R n D y k)
        else Expr.equal (uExpr L R n D x k) (uExpr L R n D y k))))

lemma questionExpr_nonzero (t : Table L R) (x y c : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (e : Fin t.ne)
    (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) (he : c.eval t.bits a=e.val) (h : Fin n) :
    (questionExpr L R n D x y c h).eval t.bits a≠0 ↔
      QuestionStep t.lc h e ((nodeEquiv L R n D t.nu t.nv).symm i).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm i).1.2
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.2 := by
  simp only [questionExpr,Expr.eval,Expr.equal_eval,Expr.listAll_eval,
    uExpr_eval L R n D t x a i hi,vExpr_eval L R n D t y a j hj,
    fieldExpr_eval t a c e he ⟨0,by omega⟩,fieldExpr_eval t a c e he ⟨1,by omega⟩]
  have indicator (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)≠0 ↔ P := by
    split_ifs <;> simp_all
  simp only [↓reduceIte,Nat.one_ne_zero,mul_ne_zero_iff,indicator,Fin.val_inj]
  unfold QuestionStep Table.lc
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  simp only [List.mem_finRange,forall_true_left]
  apply forall_congr'
  intro k
  by_cases hk : k=h
  · simp [hk,Expr.eval]
  · by_cases hl : k.val<h.val <;> simp [hk,hl,Expr.equal_eval,
      uExpr_eval L R n D t x a i hi,uExpr_eval L R n D t y a j hj,
      vExpr_eval L R n D t x a i hi,vExpr_eval L R n D t y a j hj,Fin.val_inj]

def pointStepExpr (x y c : Expr) (h : Fin n) : Expr :=
  Expr.static3 (fun (a b : StaticPoint L R n D) (f : L → R) => if PointStep h f a b then 1 else 0)
    (pointExpr L R n D x) (pointExpr L R n D y) (fieldExpr c 2)

lemma pointStepExpr_eval (t : Table L R) (x y c : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (e : Fin t.ne)
    (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) (he : c.eval t.bits a=e.val) (h : Fin n) :
    (pointStepExpr L R n D x y c h).eval t.bits a =
      if PointStep h (t.project e) ((nodeEquiv L R n D t.nu t.nv).symm i).2
        ((nodeEquiv L R n D t.nu t.nv).symm j).2 then 1 else 0 := by
  apply Expr.static3_eval
  · exact pointExpr_eval L R n D t x a i hi
  · exact pointExpr_eval L R n D t y a j hj
  · exact fieldExpr_eval t a c e he ⟨2,by omega⟩

def forwardExpr (x y : Expr) : Expr :=
  .sum neExpr (Expr.listSum (List.finRange n) (fun h =>
    .mul (pointStepExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)
      (questionExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)))

lemma forwardExpr_nonzero (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (forwardExpr L R n D x y).eval t.bits a≠0 ↔
      (layeredSystem t.lc n).ForwardZero D (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j) := by
  dsimp only [names,nodeDecode]
  rw [forward_iff]
  change _ ↔ ∃ h e, PointStep h (t.project e) ((nodeEquiv L R n D t.nu t.nv).symm i).2
    ((nodeEquiv L R n D t.nu t.nv).symm j).2 ∧ QuestionStep t.lc h e _ _ _ _
  simp only [forwardExpr,Expr.sum_ne_zero,neExpr_eval,Expr.listSum_ne_zero,List.mem_finRange,true_and]
  have each (c : ℕ) (hc : c<t.ne) (h : Fin n) :
      (Expr.mul (pointStepExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)
        (questionExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)).eval
        t.bits (Expr.bind a c)≠0 ↔
      PointStep h (t.project ⟨c,hc⟩) ((nodeEquiv L R n D t.nu t.nv).symm i).2
        ((nodeEquiv L R n D t.nu t.nv).symm j).2 ∧ QuestionStep t.lc h ⟨c,hc⟩
          ((nodeEquiv L R n D t.nu t.nv).symm i).1.1
          ((nodeEquiv L R n D t.nu t.nv).symm j).1.1
          ((nodeEquiv L R n D t.nu t.nv).symm i).1.2
          ((nodeEquiv L R n D t.nu t.nv).symm j).1.2 := by
    have hx : (x.rename Nat.succ).eval t.bits (Expr.bind a c)=i.val := by simpa [Expr.bind] using hi
    have hy : (y.rename Nat.succ).eval t.bits (Expr.bind a c)=j.val := by simpa [Expr.bind] using hj
    rw [Expr.eval,mul_ne_zero_iff,pointStepExpr_eval L R n D t _ _ _ _ i j ⟨c,hc⟩ hx hy rfl h,
      questionExpr_nonzero L R n D t _ _ _ _ i j ⟨c,hc⟩ hx hy rfl h]
    split_ifs <;> simp_all
  constructor
  · rintro ⟨c,hc,h,hh⟩; exact ⟨h,⟨c,hc⟩,(each c hc h).mp hh⟩
  · rintro ⟨h,e,hh⟩; exact ⟨e.val,e.isLt,h,(each e.val e.isLt h).mpr hh⟩

def levelExpr (x : Expr) : Expr :=
  Expr.staticLookup (fun a : StaticPoint L R n D => a.1.val) (pointExpr L R n D x)

lemma levelExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (levelExpr L R n D x).eval t.bits a=((nodeEquiv L R n D t.nu t.nv).symm i).2.1.val := by
  exact Expr.staticLookup_eval _ _ _ _ _ (pointExpr_eval L R n D t x a i hi)

def sameQuestionExpr (x y : Expr) : Expr :=
  .mul (Expr.equal (levelExpr L R n D x) (levelExpr L R n D y))
    (Expr.listAll (List.finRange n) (fun k =>
      Expr.cond (Expr.lt (.const k.val) (levelExpr L R n D x))
        (Expr.equal (vExpr L R n D x k) (vExpr L R n D y k))
        (Expr.equal (uExpr L R n D x k) (uExpr L R n D y k))))

lemma sameQuestionExpr_nonzero (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (sameQuestionExpr L R n D x y).eval t.bits a≠0 ↔
      sameQuestion L R n D ((nodeEquiv L R n D t.nu t.nv).symm i).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm i).1.2
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.2
        ((nodeEquiv L R n D t.nu t.nv).symm i).2
        ((nodeEquiv L R n D t.nu t.nv).symm j).2 := by
  have indicator (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)≠0 ↔ P := by
    split_ifs <;> simp_all
  simp only [sameQuestionExpr,Expr.eval,mul_ne_zero_iff,Expr.equal_eval,Expr.listAll_eval,
    levelExpr_eval L R n D t x a i hi,levelExpr_eval L R n D t y a j hj,
    indicator,Fin.val_inj,List.mem_finRange,forall_true_left,sameQuestion]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  simp only [Expr.cond_eval,Expr.lt_eval,Expr.eval,levelExpr_eval L R n D t x a i hi,
    indicator,Expr.equal_eval,vExpr_eval L R n D t x a i hi,vExpr_eval L R n D t y a j hj,
    uExpr_eval L R n D t x a i hi,uExpr_eval L R n D t y a j hj]
  split_ifs <;> simp_all [Fin.val_inj]

def copyCostExpr (x y : Expr) : Expr :=
  Expr.cond (sameQuestionExpr L R n D x y)
    (Expr.static2 (pointCost L R n D) (pointExpr L R n D x) (pointExpr L R n D y))
    (.const (D+1))

lemma copyCostExpr_eval (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (copyCostExpr L R n D x y).eval t.bits a=
      (Capped.clip D (copyCost (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j))).val := by
  dsimp only [names,nodeDecode]
  rw [copyCost_same]
  simp only [copyCostExpr,Expr.cond_eval,sameQuestionExpr_nonzero L R n D t x y a i j hi hj,
    Expr.static2_eval _ _ _ _ _ _ _ (pointExpr_eval L R n D t x a i hi)
      (pointExpr_eval L R n D t y a j hj),Expr.eval]

def costExpr (x y : Expr) : Expr :=
  Expr.cond (.add (forwardExpr L R n D x y) (forwardExpr L R n D y x))
    (.const 0) (copyCostExpr L R n D x y)

lemma costExpr_eval (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (costExpr L R n D x y).eval t.bits a=
      (Capped.clip D (linkCost (layeredSystem t.lc n)
        (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j))).val := by
  have add_ne (a b : ℕ) : a+b≠0 ↔ a≠0 ∨ b≠0 := by omega
  simp only [costExpr,Expr.cond_eval,Expr.eval,add_ne,
    forwardExpr_nonzero L R n D t x y a i j hi hj,
    forwardExpr_nonzero L R n D t y x a j i hj hi,
    copyCostExpr_eval L R n D t x y a i j hi hj,linkCost,ProjectionSystem.ZeroLink]
  split_ifs <;> simp_all [Capped.clip]

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FloydLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.StoredFloyd
open ShortestPaths
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open Turing

structure Input (B : ℕ) where
  n : ℕ
  matrix : Capped.Matrix B n

def Input.initial {B : ℕ} (a : Input B) : State B := ⟨a.n,0,a.matrix⟩

def Input.output {B : ℕ} (a : Input B) : State B := ⟨a.n,a.n,a.matrix.allPairs⟩

lemma run_append {B n : ℕ} (a : Capped.Matrix B n) (xs ys : List (Fin n)) :
    a.run (xs++ys) = (a.run xs).run ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact ih (a.pivot x)

lemma iterate_initial {B : ℕ} (a : Input B) (i : ℕ) (hi : i≤a.n) :
    State.step^[i] a.initial = ⟨a.n,i,a.matrix.run ((List.finRange a.n).take i)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hn : i<a.n := hi
    rw [Function.iterate_succ_apply',ih hn.le]
    have hl : i<(List.finRange a.n).length := by simpa using hn
    rw [List.take_succ_eq_append_getElem hl]
    simp only [List.getElem_finRange,run_append,Capped.Matrix.run]
    simp only [State.step,dite_eq_left hn]
    congr 2

lemma iterate_output {B : ℕ} (a : Input B) : State.step^[a.n] a.initial = a.output := by
  rw [iterate_initial a a.n le_rfl]
  simp only [Input.output,Capped.Matrix.allPairs]
  rw [List.take_of_length_le (by simp)]

lemma entry_le {B n : ℕ} (a : Capped.Matrix B n) (i j : ℕ) : entry a i j≤B+1 := by
  unfold entry
  split
  · split
    · exact (a.get _ _).bound
    · omega
  · omega

lemma value_le {B : ℕ} (s : State B) (i : ℕ) : s.value i ≤ s.n+s.k+B+1 := by
  unfold State.value
  split
  · omega
  · split
    · omega
    · have := entry_le s.matrix ((i-2)/s.n) ((i-2)%s.n); omega

end LargeIndependentSets.StoredFloyd
namespace LargeIndependentSets.FloydCarry
open IndependentSetsCut.CounterMachine
open ShortestPaths
open Turing
open scoped BigOperators
open IndependentSetsGames.Foundations.Complexity

structure State (B : ℕ) where
  core : StoredFloyd.State B
  payload : List ℕ

def State.value {B : ℕ} (s : State B) (w : ℕ) : ℕ :=
  if w<2+s.core.n*s.core.n then s.core.value w
  else if w=2+s.core.n*s.core.n then s.payload.length
  else s.payload[w-(3+s.core.n*s.core.n)]?.getD 0

def State.count {B : ℕ} (s : State B) := 3+s.core.n*s.core.n+s.payload.length
def State.bits {B : ℕ} (s : State B) := UnaryTables.words s.value s.count

def State.step {B : ℕ} (s : State B) : State B := ⟨s.core.step,s.payload⟩

lemma read_core {B : ℕ} (s : State B) (w : ℕ) (hw : w<2+s.core.n*s.core.n) :
    Expr.wordValue s.bits w=s.core.value w := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by unfold State.count; omega)]
  simp [State.value,hw]
@[simp] lemma read_n {B : ℕ} (s : State B) : Expr.wordValue s.bits 0=s.core.n := by
  rw [read_core _ _ (by omega)]; simp [StoredFloyd.State.value]
@[simp] lemma read_k {B : ℕ} (s : State B) : Expr.wordValue s.bits 1=s.core.k := by
  rw [read_core _ _ (by omega)]; simp [StoredFloyd.State.value]
@[simp] lemma read_count {B : ℕ} (s : State B) :
    Expr.wordValue s.bits (2+s.core.n*s.core.n)=s.payload.length := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by unfold State.count; omega)]
  simp [State.value]
lemma read_payload {B : ℕ} (s : State B) (w : ℕ) (hw : w < s.payload.length) :
    Expr.wordValue s.bits (3+s.core.n*s.core.n+w)=s.payload[w] := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by unfold State.count; omega)]
  simp [State.value,show ¬3+s.core.n*s.core.n+w<2+s.core.n*s.core.n by omega,
    show 3+s.core.n*s.core.n+w ≠ 2+s.core.n*s.core.n by omega,
    show 3+s.core.n*s.core.n+w-(3+s.core.n*s.core.n)=w by omega,hw]

lemma read_cell {B : ℕ} (s : State B) (i j : Fin s.core.n) :
    Expr.wordValue s.bits (2+i.val*s.core.n+j.val)=(s.core.matrix.get i j).val := by
  have hlt : i.val*s.core.n+j.val < s.core.n*s.core.n := by
    calc
      _ < (i.val+1)*s.core.n := by nlinarith [j.isLt]
      _ ≤ _ := Nat.mul_le_mul_right _ i.isLt
  rw [read_core _ _ (by omega)]
  rw [← StoredFloyd.read_cell s.core i j,StoredFloyd.State.bits,
    UnaryTables.wordValue_words _ _ _ (by omega)]

@[simp] lemma sizeExpr_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    StoredFloyd.sizeExpr.eval s.bits a=s.core.n := by simp [StoredFloyd.sizeExpr,Expr.eval]
@[simp] lemma pivotExpr_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    StoredFloyd.pivotExpr.eval s.bits a=s.core.k := by simp [StoredFloyd.pivotExpr,Expr.eval]
@[simp] lemma coreCount_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    StoredFloyd.countExpr.eval s.bits a=2+s.core.n*s.core.n := by simp [StoredFloyd.countExpr,Expr.eval]

def payloadCountExpr : Expr := Expr.word StoredFloyd.countExpr

def countExpr : Expr := .add (.add StoredFloyd.countExpr (.const 1)) payloadCountExpr

def valueExpr (B : ℕ) : Expr :=
  Expr.cond (Expr.lt (.arg 0) StoredFloyd.countExpr) (StoredFloyd.valueExpr B) (Expr.word (.arg 0))

lemma coreValue_eval {B : ℕ} (s : State B) (w : ℕ) (hw : w<2+s.core.n*s.core.n) :
    (StoredFloyd.valueExpr B).eval s.bits (fun _ => w)=s.core.step.value w := by
  by_cases hw0 : w=0
  · subst w; simp [StoredFloyd.valueExpr,Expr.eval,StoredFloyd.State.value,StoredFloyd.State.step]
  by_cases hw1 : w=1
  · subst w; simp [StoredFloyd.valueExpr,Expr.eval,StoredFloyd.State.value,StoredFloyd.State.step]
  have hw2 : 2 ≤ w := by omega
  have ht : w-2 < s.core.n*s.core.n := by omega
  have hn : 0 < s.core.n := by nlinarith
  have hi : (w-2)/s.core.n < s.core.n := (Nat.div_lt_iff_lt_mul hn).mpr ht
  have hj : (w-2)%s.core.n < s.core.n := Nat.mod_lt _ hn
  let i : Fin s.core.n := ⟨(w-2)/s.core.n,hi⟩
  let j : Fin s.core.n := ⟨(w-2)%s.core.n,hj⟩
  have hr : StoredFloyd.rowExpr.eval s.bits (fun _ => w)=i.val := by simp [StoredFloyd.rowExpr,Expr.eval,i]
  have hc : StoredFloyd.colExpr.eval s.bits (fun _ => w)=j.val := by simp [StoredFloyd.colExpr,Expr.eval,j]
  simp only [StoredFloyd.valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,hw0,hw1,ite_false,
    ne_eq,not_true_eq_false,
    sizeExpr_eval,pivotExpr_eval,Expr.lt_eval,StoredFloyd.minExpr_eval,StoredFloyd.cellExpr_eval,hr,hc]
  by_cases hk : s.core.k < s.core.n
  · let k : Fin s.core.n := ⟨s.core.k,hk⟩
    simp only [hk,ite_true,Nat.one_ne_zero,not_false_eq_true]
    rw [read_cell s i j,show s.core.k=k.val from rfl,read_cell s i k,read_cell s k j]
    simp [StoredFloyd.State.value,StoredFloyd.State.step,hw0,hw1,hk,
      StoredFloyd.entry,hi,hj,Capped.Matrix.pivot,Capped.Matrix.get,pivot,Capped.min_val,Capped.add_val,i,j,k]
  · simp only [hk,ite_false,not_true_eq_false,read_cell]
    simp [StoredFloyd.State.value,StoredFloyd.State.step,hw0,hw1,hk,StoredFloyd.entry,hi,hj,i,j]

@[simp] lemma payloadCount_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    payloadCountExpr.eval s.bits a=s.payload.length := by simp [payloadCountExpr,Expr.word_eval]
@[simp] lemma countExpr_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    countExpr.eval s.bits a=s.count := by simp [countExpr,Expr.eval,State.count]; omega

lemma valueExpr_eval {B : ℕ} (s : State B) (w : ℕ) (hw : w < s.count) :
    (valueExpr B).eval s.bits (fun _ => w)=s.step.value w := by
  simp only [valueExpr,Expr.cond_eval,Expr.lt_eval,Expr.eval,coreCount_eval]
  by_cases hc : w<2+s.core.n*s.core.n
  · simp [hc,coreValue_eval s w hc,State.value,State.step,StoredFloyd.State.step]
  · simp only [hc,ite_false,ne_eq,not_true_eq_false,Expr.word_eval,Expr.eval]
    rw [State.bits,UnaryTables.wordValue_words _ _ _ hw]
    simp only [State.value,State.step,StoredFloyd.State.step,hc,ite_false]
    rfl

lemma body_spec {B : ℕ} (s : State B) :
    UnaryTables.words (fun w => (valueExpr B).eval s.bits (fun _ => w))
      (countExpr.eval s.bits (fun _ => 0))=s.step.bits := by
  rw [countExpr_eval]
  exact UnaryTables.words_congr (valueExpr_eval s)

noncomputable def body (B : ℕ) : TM2ComputableInPolyTime State.bits State.bits (@State.step B) :=
  UnaryTables.encodedComputer _ _ _ countExpr (valueExpr B) body_spec

structure Input (B : ℕ) where
  core : StoredFloyd.Input B
  payload : List ℕ

def Input.initial {B : ℕ} (a : Input B) : State B := ⟨a.core.initial,a.payload⟩
def Input.count {B : ℕ} (a : Input B) := a.core.n
def Input.bits {B : ℕ} (a : Input B) : List Bool :=
  BoundedIteration.counted Input.count State.bits Input.initial a

def Input.output {B : ℕ} (a : Input B) : State B := ⟨a.core.output,a.payload⟩

lemma iterate_pair {B : ℕ} (s : State B) (i : ℕ) :
    State.step^[i] s=⟨StoredFloyd.State.step^[i] s.core,s.payload⟩ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

lemma iterate_output {B : ℕ} (a : Input B) : State.step^[a.count] a.initial=a.output := by
  rw [iterate_pair]
  dsimp only [Input.initial,Input.count,Input.output]
  rw [StoredFloyd.iterate_output]

lemma wordValue_le_length (s : List Bool) (w : ℕ) : Expr.wordValue s w ≤ s.length := by
  unfold Expr.wordValue
  calc
    _ ≤ ∑ _ ∈ Finset.range s.length, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold Expr.bitValue
      split <;> split <;> simp
    _ = _ := by simp

lemma bits_length_le {B : ℕ} (s : State B) (N : ℕ)
    (hn : s.core.n≤N) (hk : s.core.k≤N) (hc : s.payload.length≤N)
    (hp : ∀ w : ℕ, s.payload[w]?.getD 0≤N) :
    s.bits.length≤(3+N*N+N)*(2*N+B+2) := by
  rw [State.bits,UnaryTables.words_length]
  unfold UnaryTables.offset
  calc
    _ ≤ ∑ _ ∈ Finset.range s.count, (2*N+B+2) := by
      apply Finset.sum_le_sum
      intro w _hw
      have hv : s.value w≤2*N+B+1 := by
        unfold State.value
        split
        · have := StoredFloyd.value_le s.core w; omega
        · split
          · omega
          · have := hp (w-(3+s.core.n*s.core.n)); omega
      omega
    _ = s.count*(2*N+B+2) := by simp
    _ ≤ _ := by unfold State.count; gcongr

end LargeIndependentSets.FloydCarry

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryInitialize
attribute [-instance] _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def integerMatrix (t : Table L R) : ShortestPaths.Matrix (size L R n D t) :=
  Vector.ofFn (fun i => Vector.ofFn (fun j =>
    linkCost (layeredSystem t.lc n) (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j)))

def input (t : Table L R) : FloydCarry.Input D :=
  ⟨⟨size L R n D t,Capped.Matrix.ofInteger D (integerMatrix L R n D t)⟩,
    (List.range (3+3*t.ne)).map t.value⟩

lemma payload_length (t : Table L R) : (input L R n D t).payload.length=3+3*t.ne := by simp [input]
lemma payload_get (t : Table L R) (w : ℕ) (hw : w<3+3*t.ne) :
    (input L R n D t).payload[w]?.getD 0=t.value w := by simp [input,hw]

abbrev inputCount (t : Table L R) := 4+(size L R n D t)*(size L R n D t)+(3+3*t.ne)
def inputValue (t : Table L R) (w : ℕ) : ℕ :=
  if w=0 then size L R n D t else (input L R n D t).initial.value (w-1)

def inputCountExpr : Expr := .add (.add (.const 4) (.mul (sizeExpr L R n D) (sizeExpr L R n D)))
  (.add (.const 3) (.mul (.const 3) neExpr))

def inputValueExpr : Expr :=
  Expr.cond (Expr.lt (.arg 0) (.const 2)) (sizeExpr L R n D)
    (Expr.cond (Expr.equal (.arg 0) (.const 2)) (.const 0)
      (Expr.cond (Expr.lt (.arg 0) (.add (.const 3) (.mul (sizeExpr L R n D) (sizeExpr L R n D))))
        (costExpr L R n D (Expr.quotient (.sub (.arg 0) (.const 3)) (sizeExpr L R n D))
          (Expr.remainder (.sub (.arg 0) (.const 3)) (sizeExpr L R n D)))
        (Expr.cond (Expr.equal (.arg 0) (.add (.const 3) (.mul (sizeExpr L R n D) (sizeExpr L R n D))))
          (.add (.const 3) (.mul (.const 3) neExpr))
          (Expr.word (.sub (.arg 0) (.add (.const 4) (.mul (sizeExpr L R n D) (sizeExpr L R n D))))))))

@[simp] lemma inputCountExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    (inputCountExpr L R n D).eval t.bits a=inputCount L R n D t := by
  simp [inputCountExpr,Expr.eval,inputCount]

lemma inputValueExpr_eval (t : Table L R) (w : ℕ) (hw : w < inputCount L R n D t) :
    (inputValueExpr L R n D).eval t.bits (fun _ => w)=inputValue L R n D t w := by
  let N := size L R n D t
  have hN : 0<N := size_pos L R n D t
  have hc : (input L R n D t).initial.core.n=N := rfl
  have hk : (input L R n D t).initial.core.k=0 := rfl
  have hp : (input L R n D t).initial.payload=(input L R n D t).payload := rfl
  have indicator (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)≠0 ↔ P := by
    split_ifs <;> simp_all
  simp only [inputValueExpr,Expr.cond_eval,Expr.lt_eval,Expr.equal_eval,Expr.eval,sizeExpr_eval,neExpr_eval,indicator]
  have hsize : N=size L R n D t := rfl
  simp only [← hsize]
  by_cases hsmall : w<2
  · have hw' : w=0 ∨ w=1 := by omega
    rcases hw' with rfl | rfl <;>
      simp [inputValue,FloydCarry.State.value,StoredFloyd.State.value,hc,N]
  · simp only [hsmall,ite_false,ne_eq,not_true_eq_false]
    by_cases hw2 : w=2
    · subst w
      simp [inputValue,FloydCarry.State.value,StoredFloyd.State.value,hc,hk,N,show (1:ℕ)<2+N*N by omega]
    · have hw3 : 3≤w := by omega
      simp only [hw2,ite_false,not_true_eq_false]
      by_cases hmat : w<3+N*N
      · have hi : (w-3)/N<N := (Nat.div_lt_iff_lt_mul hN).mpr (by omega)
        have hj : (w-3)%N<N := Nat.mod_lt _ hN
        let i : Fin N := ⟨(w-3)/N,hi⟩
        let j : Fin N := ⟨(w-3)%N,hj⟩
        have hei : (Expr.quotient (.sub (.arg 0) (.const 3)) (sizeExpr L R n D)).eval t.bits (fun _ => w)=i.val := by
          simp [Expr.quotient_eval,Expr.eval,i,N]
        have hej : (Expr.remainder (.sub (.arg 0) (.const 3)) (sizeExpr L R n D)).eval t.bits (fun _ => w)=j.val := by
          simp [Expr.remainder_eval,Expr.eval,j,N]
        simp only [hmat,ite_true]
        rw [costExpr_eval L R n D t _ _ _ i j hei hej]
        simp [inputValue,FloydCarry.State.value,show w≠0 by omega,
          show w-1<2+N*N by omega,StoredFloyd.State.value,show w-1≠0 by omega,
          show w-1≠1 by omega,show w-1-2=w-3 by omega,
          input,FloydCarry.Input.initial,StoredFloyd.Input.initial,StoredFloyd.entry,hi,hj,
          Capped.Matrix.ofInteger,Capped.Matrix.get,integerMatrix,ShortestPaths.Matrix.get,i,j,N]
      · simp only [hmat,ite_false]
        by_cases hend : w=3+N*N
        · simp only [hend,ite_true]
          simp [inputValue,FloydCarry.State.value,hc,hp,payload_length,N]
        · simp only [hend,ite_false,Expr.word_eval,Expr.eval,sizeExpr_eval]
          have hoff : w-(4+N*N)<3+3*t.ne := by change w < 4+N*N+(3+3*t.ne) at hw; omega
          rw [Table.bits,UnaryTables.wordValue_words _ _ _ hoff]
          simp [inputValue,FloydCarry.State.value,hc,hp,show w≠0 by omega,
            show ¬w-1<2+N*N by omega,show w-1≠2+N*N by omega,
            show w-1-(3+N*N)=w-(4+N*N) by omega,payload_get L R n D t _ hoff,N]

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def distances (t : Table L R) := (input L R n D t).output

abbrev prefixCount (t : Table L R) := 3+size L R n D t*size L R n D t

def payloadOffsetExpr : Expr :=
  .sum (.add (.const 3) (.mul StoredFloyd.sizeExpr StoredFloyd.sizeExpr))
    (.add (Expr.word (.arg 0)) (.const 1))

def fromTable (e : Expr) : Expr := Expr.dropInput payloadOffsetExpr e

lemma distances_suffix (t : Table L R) :
    (distances L R n D t).bits =
      UnaryTables.words (distances L R n D t).value (prefixCount L R n D t) ++ t.bits := by
  have hc : (distances L R n D t).count=prefixCount L R n D t+(3+3*t.ne) := by
    simp [distances,FloydCarry.Input.output,FloydCarry.State.count,StoredFloyd.Input.output,input,prefixCount]
  rw [FloydCarry.State.bits,hc,UnaryTables.words_add]
  congr 1
  apply UnaryTables.words_congr
  intro w hw
  have hprefix : (distances L R n D t).core.n=size L R n D t := rfl
  simp only [FloydCarry.State.value,hprefix]
  have hn : ¬prefixCount L R n D t+w<2+size L R n D t*size L R n D t := by unfold prefixCount; omega
  have he : prefixCount L R n D t+w≠2+size L R n D t*size L R n D t := by unfold prefixCount; omega
  rw [ite_eq_right hn,ite_eq_right he]
  have hs : prefixCount L R n D t+w-(3+size L R n D t*size L R n D t)=w := by unfold prefixCount; omega
  rw [hs]
  exact payload_get L R n D t w hw

lemma payloadOffsetExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    payloadOffsetExpr.eval (distances L R n D t).bits a=
      (UnaryTables.words (distances L R n D t).value (prefixCount L R n D t)).length := by
  simp only [payloadOffsetExpr,Expr.eval,FloydCarry.sizeExpr_eval,UnaryTables.words_length,UnaryTables.offset]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Expr.word_eval,Expr.eval]
  rw [FloydCarry.State.bits,UnaryTables.wordValue_words]
  · rfl
  · change w < 3+(size L R n D t)*(size L R n D t)+(input L R n D t).payload.length
    exact lt_of_lt_of_le (Finset.mem_range.mp hw) (Nat.le_add_right _ _)

lemma fromTable_eval (e : Expr) (t : Table L R) (a : ℕ → ℕ) :
    (fromTable e).eval (distances L R n D t).bits a=e.eval t.bits a := by
  rw [fromTable,Expr.dropInput_eval,payloadOffsetExpr_eval,distances_suffix,List.drop_left]

def closeExpr (i j : Expr) : Expr := Expr.le (StoredFloyd.cellExpr i j) (.const (D/8))

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GeometryPointTable
attribute [-instance] _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC
open scoped Classical
noncomputable section
variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def pointLookup (f : StaticPoint L R n D → ℕ) (x : Expr) : Expr :=
  Expr.finLookup (fun i => f ((pointEquiv L R n D).symm i)) x

lemma pointLookup_eval (f : StaticPoint L R n D → ℕ) (x : Expr) (s : List Bool) (a : ℕ → ℕ)
    (v : StaticPoint L R n D) (hv : x.eval s a=(pointEquiv L R n D v).val) :
    (pointLookup L R n D f x).eval s a=f v := by
  rw [pointLookup,Expr.finLookup_eval _ _ _ _ (pointEquiv L R n D v) hv,Equiv.symm_apply_apply]

lemma pointExpr_code (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (pointExpr L R n D x).eval t.bits a=
      (pointEquiv L R n D ((nodeEquiv L R n D t.nu t.nv).symm i).2).val :=
  pointExpr_eval L R n D t x a i hi

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryAntipodes
attribute [-instance] _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def antiName (t : Table L R) (i : Fin (size L R n D t)) : Fin (size L R n D t) :=
  nodeEquiv L R n D t.nu t.nv
    (((nodeEquiv L R n D t.nu t.nv).symm i).1,antiPoint L R n D ((nodeEquiv L R n D t.nu t.nv).symm i).2)

def antiExpr (x : Expr) : Expr :=
  .add (.mul (Expr.quotient x (.const (staticCount L R n D))) (.const (staticCount L R n D)))
    (pointLookup L R n D (fun a : StaticPoint L R n D => (pointEquiv L R n D (antiPoint L R n D a)).val)
      (pointExpr L R n D x))

lemma antiExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (antiExpr L R n D x).eval t.bits a=(antiName L R n D t i).val := by
  simp only [antiExpr,Expr.eval,Expr.quotient_eval,hi]
  rw [pointLookup_eval L R n D _ _ _ _ ((nodeEquiv L R n D t.nu t.nv).symm i).2
    (pointExpr_code L R n D t x a i hi)]
  have he : (finFunctionFinEquiv (((nodeEquiv L R n D t.nu t.nv).symm i).1.1)).val=
      ((finProdFinEquiv.symm (finProdFinEquiv.symm i).1).1).val := by
    change (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  have he' : (finFunctionFinEquiv (((nodeEquiv L R n D t.nu t.nv).symm i).1.2)).val=
      ((finProdFinEquiv.symm (finProdFinEquiv.symm i).1).2).val := by
    change (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [antiName,nodeEquiv_val,he,he']
  simp only [finProdFinEquiv,Equiv.coe_fn_symm_mk,Fin.divNat,Fin.modNat]
  have h := Nat.mod_add_div (i.val/staticCount L R n D) (t.nv^n)
  rw [h]
  ring

def payloadApply (e x : Expr) : Expr := (fromTable e).subst (fun _ => x)

lemma payloadApply_eval (t : Table L R) (e x : Expr) (a : ℕ → ℕ) :
    (payloadApply e x).eval (distances L R n D t).bits a=
      e.eval t.bits (fun _ => x.eval (distances L R n D t).bits a) := by
  rw [payloadApply,Expr.subst_eval,fromTable_eval]

def antiDistanceExpr (x : Expr) : Expr := payloadApply (antiExpr L R n D (.arg 0)) x

def cliqueExpr : Expr := .sum StoredFloyd.sizeExpr
  (closeExpr D (.arg 0) (antiDistanceExpr L R n D (.arg 0)))

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryLocations
attribute [-instance] _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC PhaseTest Coefficient
open scoped Classical BigOperators
noncomputable section
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

variable (L R : Type) [Fintype L] [Fintype R] (p : SamplerParameters)

abbrev Outcome := (p.law L R).Expanded
abbrev outcomeCount := Fintype.card (Outcome L R p)
abbrev vertexCount (t : Table L R) := t.ne^p.n*outcomeCount L R p

lemma vertexCount_pos (t : Table L R) : 0<vertexCount L R p t :=
  Nat.mul_pos (pow_pos t.he _) Fintype.card_pos

def vertexEquiv (t : Table L R) : p.Vertices L R (Fin t.ne) ≃ Fin (vertexCount L R p t) :=
  (Equiv.prodCongr finFunctionFinEquiv (Fintype.equivFin (Outcome L R p))).trans finProdFinEquiv

def samplePoint (f : Fin p.n → L → R) (o : Outcome L R p) : StaticPoint L R p.n (p.m*2^p.k) :=
  ⟨(p.location (scheduleLC L R p f) (id,o)).1.1,
    (p.location (scheduleLC L R p f) (id,o)).2⟩

def vertexCountExpr : Expr := .mul (Expr.power neExpr p.n) (.const (outcomeCount L R p))
def outcomeExpr (x : Expr) : Expr := Expr.remainder x (.const (outcomeCount L R p))
def chainExpr (x : Expr) (k : Fin p.n) : Expr :=
  Expr.remainder (Expr.quotient (Expr.quotient x (.const (outcomeCount L R p)))
    (Expr.power neExpr k.val)) neExpr

@[simp] lemma vertexCountExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    (vertexCountExpr L R p).eval t.bits a=vertexCount L R p t := by
  simp [vertexCountExpr,Expr.eval,vertexCount]

def scheduleTest (x : Expr) (f : Fin p.n → L → R) : Expr :=
  Expr.listAll (List.finRange p.n) fun k =>
    Expr.equal (fieldExpr (chainExpr L R p x k) 2) (.const (projectCode (f k)))

def scheduleCodeExpr (x : Expr) : Expr :=
  Expr.pick (fun f : Fin p.n → L → R => (Fintype.equivFin _ f).val) (scheduleTest L R p x)

def samplePointExpr (x : Expr) : Expr :=
  Expr.static2 (fun f o => (pointEquiv L R p.n (p.m*2^p.k) (samplePoint L R p f o)).val)
    (scheduleCodeExpr L R p x) (outcomeExpr L R p x)

def tupleCodeExpr (base : Expr) (f : Fin p.n → Expr) : Expr :=
  Expr.listSum (List.finRange p.n) (fun k => .mul (f k) (Expr.power base k.val))

def locationExpr (x : Expr) : Expr :=
  .add (.mul (.add (.mul (tupleCodeExpr p nuExpr (fun k => fieldExpr (chainExpr L R p x k) 0))
        (Expr.power nvExpr p.n))
      (tupleCodeExpr p nvExpr (fun k => fieldExpr (chainExpr L R p x k) 1)))
      (.const (staticCount L R p.n (p.m*2^p.k)))) (samplePointExpr L R p x)

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

variable (L R : Type) [Fintype L] [Fintype R] (p : SamplerParameters) (q : ℕ) (hq : 0<q)

def output (t : Table L R) : Graph :=
  if p.CliqueTest t.lc then Graph.clique q hq
  else Graph.ofEnumeration (p.graph t.lc) (vertexCount_pos L R p t) (vertexEquiv L R p t).symm

def locationDistanceExpr (x : Expr) : Expr := payloadApply (locationExpr L R p (.arg 0)) x

def outputCountExpr : Expr := Expr.cond (cliqueExpr L R p.n (p.m*2^p.k)) (.const q)
  (fromTable (vertexCountExpr L R p))

def adjacencyExpr (x y : Expr) : Expr :=
  .mul (.zero (Expr.equal x y)) (Expr.cond (cliqueExpr L R p.n (p.m*2^p.k)) (.const 1)
    (closeExpr (p.m*2^p.k) (locationDistanceExpr L R p x)
      (antiDistanceExpr L R p.n (p.m*2^p.k) (locationDistanceExpr L R p y))))

def flatAdjacencyExpr : Expr := adjacencyExpr L R p
  (Expr.quotient (.arg 0) (outputCountExpr L R p q))
  (Expr.remainder (.arg 0) (outputCountExpr L R p q))

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachinePaddingBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddingBounds

def inputSize (v e count : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + (encodeWord count).length + output.length

theorem rowBound_le_cap (d v e count : Nat) (output : List Bool) :
    rowBound d v e count ≤ rowCap d (inputSize v e count output) := by
  have hbase : v + e + count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hcount : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hmul := Nat.mul_le_mul_right d (Nat.succ_le_succ hcount)
  have h := Nat.add_le_add_right (Nat.add_le_add hbase hmul) 8194
  simpa only [rowBound, rowCap, Nat.succ_eq_add_one, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

end IndependentSetsGames.Foundations.Complexity.MachinePaddingBounds

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachinePreservingLookupClean
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def steps (values : List Nat) (index : Nat) : Nat :=
  (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) +
    ((encodeWords (values.drop (index + 1))).length + 1)

theorem remaining_length_le (values : List Nat) (index : Nat) :
    (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop (index + 1) values)
  simp only [encodeWords_append, List.length_append] at h
  omega

end IndependentSetsGames.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRegularOriginalRow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

theorem vectorBits_eq_encodedBlock {n : Nat} (relation : Vector Bool n) :
    PoweringMachineRow.encodeBits (List.ofFn (fun i : Fin n => relation[i])) =
      encodeWords (relation.toList.map GraphTables.bitWord) := by
  rw [PoweringMachineRow.encodeBits_graphWords]
  congr 1
  congr 1
  have hvec : Vector.ofFn (fun i : Fin n => relation[i]) = relation := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList hvec)

end IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRegularMetadata
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open IndependentSetsGames.Foundations.PCP

variable {σ : Type}

theorem encodeWords_drop_length_le (values : List Nat) (n : Nat) :
    (encodeWords (values.drop n)).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop n values)
  simp only [encodeWords_append, List.length_append] at h
  omega

end IndependentSetsGames.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineUnaryLess
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem scan_step_zero_left (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, decide (0 < b)), none),
        tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  cases b <;> simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_zero_right (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, false), none),
        tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_succ (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord (b + 1) ++ rightSuffix)
        savedLeft savedRight⟩ =
      some ⟨some scanLabel, ((ambient, flag), some true),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix)
          (true :: savedLeft) (true :: savedRight)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scanTrace (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[min a b + 1]
      (some ⟨some scanLabel, ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩) =
      some ⟨some restoreLabel, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord (a - b) ++ leftSuffix) (encodeWord (b - a) ++ rightSuffix)
          (List.replicate (min a b) true ++ savedLeft) (List.replicate (min a b) true ++ savedRight)⟩ := by
  induction a generalizing b savedLeft savedRight register with
  | zero =>
    simpa using scan_step_zero_left slots scanLabel restoreLabel program atScan base b
      leftSuffix rightSuffix savedLeft savedRight ambient flag register
  | succ a ih =>
    cases b with
    | zero =>
      simpa using scan_step_zero_right slots scanLabel restoreLabel program atScan base a
        leftSuffix rightSuffix savedLeft savedRight ambient flag register
    | succ b =>
      have hm : min (a + 1) (b + 1) = min a b + 1 := by omega
      rw [hm, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ slots scanLabel restoreLabel program atScan, ih]
      have hsave (xs : List Bool) :
          List.replicate (min a b) true ++ true :: xs =
            List.replicate (min a b + 1) true ++ xs := by
        simp [List.replicate_add, List.append_assoc]
      simp only [hsave, Nat.add_sub_add_right, Nat.add_lt_add_iff_right]

end IndependentSetsGames.Foundations.Complexity.MachineUnaryLessAt

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_SelectAlphabet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]
abbrev CoreState (σ : Type) (q : Nat) :=
  (σ × (MachineFixedBlockMap.Buffer 4096 ×
    (Fin q × (Bool × MachineCloudSelect.Phase)))) × Option Bool

end IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_OldSelectSteps
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]

def coreRotorStateEquiv (σ : Type) (q : Nat) :
    MachineFixedDivMod.State
      ((σ × MachineFixedBlockMap.Buffer 4096) × (Bool × MachineCloudSelect.Phase)) q ≃
        CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2, (s.1.2, s.1.1.2))), s.2)
  invFun s := ((((s.1.1, s.1.2.1), s.1.2.2.2), s.1.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,b⟩,⟨c,d⟩⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreInitialState (q : Nat) (positive : 0 < q) (ambient : σ) : CoreState σ q :=
  ((ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking)))), none)

end IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRegularDummyRow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularDummyRow

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

end IndependentSetsGames.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem dummyMemory_update (x : Nat) (output output' : List Bool) :
    Function.update (MachineRegularDummyRow.memory x output)
      (4 : MachineRegularDummyRow.Tape) output' = MachineRegularDummyRow.memory x output' := by
  funext j; fin_cases j <;> rfl

end IndependentSetsGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev CoreState := MachineRegularInternalRow.CoreState Unit internalDegree

end IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev CoreState := MachineRegularOriginalBody.CoreState

end IndependentSetsGames.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_VertexLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineLazyRows
open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap )
variable {K Λ A : Type} [DecidableEq K]

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem reindexValue_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    MachinePortReindex.value d c b r.reverseIndex.val ≤ valueBound c b m := by
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hmod := (Nat.mod_le r.reverseIndex.val d).trans hj
  have hmul := Nat.mul_le_mul_left c hdiv
  unfold MachinePortReindex.value valueBound
  omega

end IndependentSetsGames.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingFinishRuntime

open Turing IndependentSetsGames.Foundations.Complexity
open PreprocessingRegularTables

theorem finish_degree_positive (d : Nat) (hd : 0 < d) : 0 < d + internalDegree :=
  hd.trans_le (Nat.le_add_right d internalDegree)

end IndependentSetsGames.Foundations.PCP.PreprocessingFinishRuntime

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineFinish
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

def afterD (output : K) (base : K → List Bool) (m : Nat) : K → List Bool :=
  Function.update base output (encodeWord m ++ base output)

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

def steps (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + MachineDrainMany.steps (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m)

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

theorem steps_le_uniform (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    steps enumeration output base n m ≤ 2 * (n + m) + 6 + N * (bound + n + m + 3) := by
  have hc := MachineDrainMany.steps_le_uniform (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) (bound + n + m + 2)
    (afterHeaders_length_le output base n m bound bounded)
  have hl := MachineDrainMany.workTapes_length_le enumeration output
  have hm := Nat.mul_le_mul_right (bound + n + m + 3) hl
  rw [show bound + n + m + 2 + 1 = bound + n + m + 3 by omega] at hc
  unfold steps
  rw [copySteps_eq]
  exact Nat.add_le_add_left (hc.trans hm) _

end IndependentSetsGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineRowHeaders
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

def headerPlacement {t max : Nat} (h : t ≤ max) : PoweringMachineWord.Tape t → Tape max :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)) ∘ wordPlacement h false

theorem headerPlacement_injective {t max : Nat} (h : t ≤ max) :
    Function.Injective (headerPlacement h) :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)).injective.comp (wordPlacement_injective h false)

@[simp] theorem headerPlacement_table {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 0) = table max := by
  simp [headerPlacement, table, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_query {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 1) = query max := by
  simp [headerPlacement, query, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scan {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 2) = scan max := by
  simp [headerPlacement, scan, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_reverse {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 3) = reverse max := by
  simp [headerPlacement, reverse, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scratch {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 4) = scratch max := by
  simp [headerPlacement, scratch, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_output {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 5) = rowOutput max := by
  simp [headerPlacement]

@[simp] theorem headerPlacement_start {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inr (PoweringMachineWord.first t)) = start max := by
  simp [headerPlacement, start, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_succ {t max : Nat} (h : t ≤ max) (i : Fin t) :
    headerPlacement h (.inr i.succ) = .inr (Fin.castLE h i) := by
  simp [headerPlacement, leftEndpoint, rowOutput, Equiv.swap_apply_def]

def afterReverse (n : Nat) (placement : Tape max → K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  Function.update base (placement (rowOutput max))
    (encodeWord (reverseValue d n vertex ports direction) ++ base (placement (rowOutput max)))

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRowHeaders

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineRowBody
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} {vertices d : Nat}

def headerPlacement {max : Nat} (placement : PoweringMachineTapes.Tape max → K)
    (output : K) (i : PoweringMachineTapes.Tape max) : K :=
  if i = .inl 10 then output else placement i

@[simp] theorem headerPlacement_output {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K) :
    headerPlacement placement output (.inl 10) = output := by simp [headerPlacement]

theorem headerPlacement_injective {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    Function.Injective (headerPlacement placement output) := by
  intro i j h
  by_cases hi : i = .inl 10
  · subst i
    by_cases hj : j = .inl 10
    · exact hj.symm
    · exact False.elim (outside j (by simpa [headerPlacement, hj] using h))
  · by_cases hj : j = .inl 10
    · subst j
      exact False.elim (outside i (by simpa [headerPlacement, hi] using h.symm))
    · exact distinct (by simpa [headerPlacement, hi, hj] using h)

theorem headerPlacement_excludes_data {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    ∀ i, placement (.inl 10) ≠ headerPlacement placement output i := by
  intro i h
  by_cases hi : i = .inl 10
  · subst i
    exact outside _ (by simpa only [headerPlacement_output] using h.symm)
  · have heq : (.inl 10 : PoweringMachineTapes.Tape max) = i :=
      distinct (by simpa [headerPlacement, hi] using h)
    exact hi heq.symm

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

theorem encodeWords_flatMap {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end IndependentSetsGames.Foundations.Complexity.PoweringMachineVertex

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineOuterLoop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Placement (K : Type) (n : Nat) := PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K

def counter (placement : Placement K n) (base : K → List Bool) (remaining : Nat) : K → List Bool :=
  MachineUnaryCounter.counterTapes (placement (.inl 1)) base remaining []

theorem counter_other (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (remaining : Nat) (j : Fin 11) (hj : j ≠ 1) :
    counter placement base remaining (placement (.inl j)) = base (placement (.inl j)) := by
  apply MachineUnaryCounter.counterTapes_other
  intro h
  exact hj (Sum.inl.inj (distinct h))

end IndependentSetsGames.Foundations.Complexity.PoweringMachineOuterLoop

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineGlobal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal

open Turing

abbrev Tape (n : Nat) :=
  PoweringMachineInitialize.GlobalTape (PoweringMachineRowBody.capacity n)

def placement (n : Nat) :
    PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → Tape n :=
  PoweringMachineInitialize.commonPlacement (PoweringMachineRowBody.capacity n)

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

def outputTape (n : Nat) : Tape n :=
  PoweringMachineInitialize.finalOutput (PoweringMachineRowBody.capacity n)

def headerVertices (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.vertices
def headerDarts (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.darts

def enumeration (n : Nat) :
    Fin (4 + (11 + PoweringMachineRowBody.capacity n + 1)) ≃ Tape n :=
  PoweringGlobalEnumeration.enumeration (PoweringMachineRowBody.capacity n)

end IndependentSetsGames.Foundations.Complexity.PoweringMachineGlobal

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PCPGapMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinaryNormalize
open BinarySyntax BinaryNames
open IndependentSetsGames.Foundations
open IndependentSetsCut.CounterMachine
open scoped BigOperators

@[simp] lemma annotated_input (s : List Bool) : (annotated s).input = s :=
  FiniteScan.iterate_input _ _ _ _

def finiteTableExpr {m : ℕ} (f : Fin m → Bool → ℕ) (q b : Expr) : Expr :=
  Expr.listSum (List.finRange m) (fun i => .mul (Expr.equal q (.const i.val))
    (Expr.cond b (.const (f i true)) (.const (f i false))))

lemma finiteTableExpr_eval {m : ℕ} (f : Fin m → Bool → ℕ) (q b : Expr)
    (s : List Bool) (a : ℕ → ℕ) (i : Fin m) (c : Bool)
    (hq : q.eval s a=i.val) (hb : b.eval s a=if c then 1 else 0) :
    (finiteTableExpr f q b).eval s a=f i c := by
  simp only [finiteTableExpr,Expr.listSum_eval,Expr.eval,Expr.equal_eval,Expr.cond_eval,hq,hb]
  cases c <;> simp only [Bool.false_eq_true,↓reduceIte,ne_eq,not_true_eq_false,
    one_ne_zero,not_false_eq_true]
  all_goals
    rw [← List.ofFn_eq_map,List.sum_ofFn]
    simp [Fin.val_inj]

noncomputable def tagExpr (p : Expr) : Expr :=
  finiteTableExpr (fun q b => eventCode (event (phaseEquiv.symm q) b))
    (FiniteScan.historyExpr p) (rawExpr p)

lemma tagExpr_eval (s : List Bool) (p : Expr) (a : ℕ → ℕ)
    (hp : p.eval (annotated s).bits a ≤ s.length) :
    (tagExpr p).eval (annotated s).bits a=eventCode (eventAt s (p.eval (annotated s).bits a)) := by
  unfold tagExpr
  rw [finiteTableExpr_eval _ _ _ _ _
    (phaseEquiv (run .headerMark (s.take (p.eval (annotated s).bits a))))
    (raw s (p.eval (annotated s).bits a))]
  · simp [eventAt]
  · simp only [FiniteScan.historyExpr_eval,FiniteScan.nExpr_eval,annotated_input]
    have hr := FiniteScan.read_history (annotated s) (p.eval (annotated s).bits a)
      (by simpa only [annotated_input] using hp)
    simpa only [annotated_input,annotated_history _ _ hp] using hr
  · simpa only [annotated_input] using rawExpr_eval (annotated s) p a

def sourcePositionExpr (p r j : Expr) : Expr :=
  Expr.cond (.mul (Expr.equal j (.const 1)) (Expr.le (.const 1) r)) (nextExpr p)
    (Expr.cond (.mul (Expr.equal j (.const 2)) (Expr.le (.const 2) r))
      (nextExpr (nextExpr p)) p)

lemma sourcePositionExpr_eval {m : ℕ} (s : FiniteScan.State m) (p r j : Expr) (a : ℕ → ℕ) :
    (sourcePositionExpr p r j).eval s.bits a =
      sourcePosition s.input (p.eval s.bits a) (r.eval s.bits a) (j.eval s.bits a) := by
  simp only [sourcePositionExpr,Expr.cond_eval,Expr.eval,Expr.equal_eval,Expr.le_eval,
    nextExpr_eval,sourcePosition]
  by_cases h1 : j.eval s.bits a=1 <;> by_cases h2 : j.eval s.bits a=2 <;>
    by_cases hr1 : 1 ≤ r.eval s.bits a <;> by_cases hr2 : 2 ≤ r.eval s.bits a <;>
    simp [h1,h2,hr1,hr2]

def blockExpr (p i tag : Expr) : Expr :=
  let slot := Expr.remainder (Expr.quotient i (.const 2)) (.const 3)
  let pos := sourcePositionExpr p (.sub tag (.const 2)) slot
  Expr.cond (.mul (Expr.le (.const 2) tag) (Expr.lt i (.const 6)))
    (Expr.cond (Expr.equal (Expr.remainder i (.const 2)) (.const 0)) (keyExpr pos) (rawExpr pos))
    (Expr.cond (Expr.equal (Expr.remainder i (.const 2)) (.const 0)) (.const 0)
      (Expr.cond (Expr.equal tag (.const 1)) (Expr.le (.const 6) i)
        (Expr.cond (Expr.equal slot (.const 1)) (.const 0) (.const 1))))

lemma blockExpr_eval (s : List Bool) (p i : Expr) (a : ℕ → ℕ)
    (hp : p.eval (annotated s).bits a  ≤  s.length) :
    (blockExpr p i (tagExpr p)).eval (annotated s).bits a=
      blockValue s (p.eval (annotated s).bits a) (i.eval (annotated s).bits a) := by
  simp only [blockExpr,Expr.cond_eval,Expr.eval,Expr.le_eval,Expr.lt_eval,Expr.equal_eval,
    tagExpr_eval s p a hp,keyExpr_eval,rawExpr_eval,sourcePositionExpr_eval,
    Expr.quotient_eval,Expr.remainder_eval,annotated_input]
  unfold blockValue
  by_cases ht : 2 ≤ eventCode (eventAt s (p.eval (annotated s).bits a)) <;>
    by_cases hi : i.eval (annotated s).bits a < 6 <;>
    by_cases hr : i.eval (annotated s).bits a % 2 = 0 <;>
    by_cases he : eventCode (eventAt s (p.eval (annotated s).bits a)) = 1 <;>
    by_cases hs : (i.eval (annotated s).bits a / 2) % 3 = 1 <;>
    simp [ht,hi,hr,he,hs,show (6 ≤ i.eval (annotated s).bits a) ↔
      ¬i.eval (annotated s).bits a < 6 by omega]

def countExpr : Expr := .add (.const 2) (.mul (.const 12) FiniteScan.nExpr)
noncomputable def valueExpr : Expr :=
  let p := Expr.quotient (.sub (.arg 0) (.const 2)) (.const 12)
  let i := Expr.remainder (.sub (.arg 0) (.const 2)) (.const 12)
  Expr.cond (Expr.equal (.arg 0) (.const 0)) (.add FiniteScan.nExpr (.const 1))
    (Expr.cond (Expr.equal (.arg 0) (.const 1)) (.mul (.const 2) FiniteScan.nExpr)
      (blockExpr p i (tagExpr p)))

lemma countExpr_eval (s : List Bool) (a : ℕ → ℕ) :
    countExpr.eval (annotated s).bits a=tableCount s := by
  simp [countExpr,Expr.eval,tableCount]

lemma valueExpr_eval (s : List Bool) (w : ℕ) (hw : w<tableCount s) :
    valueExpr.eval (annotated s).bits (fun _ => w)=tableValue s w := by
  have hp : (w-2)/12 ≤ s.length := by unfold tableCount at hw; omega
  have hb := blockExpr_eval s (Expr.quotient (.sub (.arg 0) (.const 2)) (.const 12))
    (Expr.remainder (.sub (.arg 0) (.const 2)) (.const 12)) (fun _ => w) (by simpa [Expr.eval] using hp)
  simp only [valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,hb,FiniteScan.nExpr_eval,annotated_input,Expr.quotient_eval,Expr.remainder_eval]
  by_cases h0 : w=0 <;> by_cases h1 : w=1 <;> simp [tableValue,h0,h1]

end LargeIndependentSets.BinaryNormalize

end OAI
end


