-- Prove2me | Definitions.Def_OAIQ241TT014
-- name    : OAIQ241TT014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:05.46543+00:00
-- url     : https://prove2.me/theorems/b4b1d4a6-8b9b-4165-a361-9dc33cf0dfb5
-- title:
--   Definitions bundle OAIQ241TT014 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 114 declarations of OpenAI's Lean: 100 definitions and 14 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.edgeActive`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.extraction`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.forms`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.fullColumn`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.fullRows`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.mask`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskBit`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.normalizationParams`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.positiveMatrix`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.reducedColumn`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.reducedEntry`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.reducedRows`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.scaledRows`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.scales`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.secondMatrix`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.signsProgram`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsifyProgram`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.targetBinary`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.targetCount`, `OAI.AlgorithmicThinTrees.InputStack.bRun`, `OAI.AlgorithmicThinTrees.InputStack.eRun`, `OAI.AlgorithmicThinTrees.InputStack.largeRun`, `OAI.AlgorithmicThinTrees.InputStack.machine`, `OAI.AlgorithmicThinTrees.InputStack.program`, `OAI.AlgorithmicThinTrees.Iteration.Stack.halveProgram`, `OAI.AlgorithmicThinTrees.Iteration.Stack.run`, `OAI.AlgorithmicThinTrees.Iteration.Stack.stepProgram`, `OAI.AlgorithmicThinTrees.Iteration.Stack.treeProgram`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.extract`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.found`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.next`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.solvePencil`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.updateProgram`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.updatedCapacity`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.updatedMatrix`, `OAI.AlgorithmicThinTrees.Normalization.Stack.isHeavy`, `OAI.AlgorithmicThinTrees.Normalization.Stack.newScales`, `OAI.AlgorithmicThinTrees.Normalization.Stack.normalized`, `OAI.AlgorithmicThinTrees.Normalization.Stack.run`, `OAI.AlgorithmicThinTrees.Normalization.Stack.step` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Complexity_PSDControllerPolynomial`, `MatrixSigning_Machines_ControllerRuntime`, `MatrixSigning_Machines_SparseCoefficientStage`, `MatrixSigning_Matrices_PivotControllerBody`, `MatrixSigning_Matrices_PivotControllerCorrectness`, `MatrixSigning_Matrices_PivotTerminalMachine`, `MatrixSigning_Optimization_TerminalWitnessMachine`, `MatrixSigning_Realization_CurvatureRealization`, `MatrixSigning_Realization_FaceChoiceRealization`, `MatrixSigning_Realization_FaceQueryRealization`, `MatrixSigning_Realization_FaceRunRealization`, `MatrixSigning_Realization_OptimizeRealization`, `MatrixSigning_Realization_OriginalSignRealization`, `MatrixSigning_Realization_PSDCleanRoutine`, `MatrixSigning_Realization_PotentialRealization`, `MatrixSigning_Realization_RoundedStepRealization`, `MatrixSigning_Realization_ScheduleRealization`, `MatrixSigning_Realization_SearchRealization`, `MatrixSigning_Realization_StencilRealization`, `MatrixSigning_Realization_StoredPSDRealization`, `MatrixSigning_Realization_ValueQueryRealization`, `MatrixSigning_Realization_VarianceRealization`, `MatrixSigning_Realization_WitnessRealization`, `ThinTrees_Continuation_Realization`, `ThinTrees_Encoding_AlgorithmicMain`, `ThinTrees_Encoding_InputDispatch`, `ThinTrees_Encoding_InputOutput`, `ThinTrees_Normalization_Realization`, `ThinTrees_Pencil_SearchRealization`, `ThinTrees_Signing_Realization`, `ThinTrees_Sparsification_IterationRealization`, `ThinTrees_Sparsification_Realization`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`; the bundles `OAIQ241TT012` and `OAIQ241TT013` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_forms`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial`, `OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns`, `OAI.CurrentKS.Realization.runsPoly_normalizedRun` and `OAI.CurrentKS.Realization.runsPoly_orbitStep`; the proofs of `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_forms`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial`, `OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns`, `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, `OAI.CurrentKS.Realization.isPoly_face_orbit`, `OAI.CurrentKS.Realization.runsPoly_normalizedRun` and `OAI.CurrentKS.Realization.runsPoly_orbitStep`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT012
import Definitions.Def_OAIQ241TT013

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SparseCoefficientStage
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SparseCoefficientStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

theorem arithmetic_spec (s : Fin 35 → List Bool) (a b : ℚ)
    (hc : ∀ i, i.val < 16 → s i = [])
    (ha : s 19 = KS.W01.encodeRat a) (hb : s 20 = KS.W01.encodeRat b)
    (h21 : s 21 = []) (h22 : s 22 = []) (h24 : s 24 = []) (h25 : s 25 = [])
    (h27 : s 27 = []) (h28 : s 28 = []) :
    RunSpec arithmetic s (after s a b) (SparseScalarNodes.ticks a b) := by
  let small := fun i => s (ports i)
  have hcore : CoreEmpty small := by
    intro i
    apply hc
    fin_cases i <;> decide
  have h := SparseScalarNodes.coefficient_spec small a b hcore ha hb h21 h22 h24 h25 h27 h28
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _ h
  · intro i; rfl
  · intro i; fin_cases i <;> simp [after,put,SparseScalarNodes.after,SparseScalarNodes.put,small,ports]
  · intro i hi
    have h24' := hi 20
    have h25' := hi 21
    have h21' := hi 18
    have h22' := hi 19
    have h27' := hi 24
    have h28' := hi 25
    change i ≠ 24 at h24'
    change i ≠ 25 at h25'
    change i ≠ 21 at h21'
    change i ≠ 22 at h22'
    change i ≠ 27 at h27'
    change i ≠ 28 at h28'
    simp [after,put,Function.update_of_ne,h24',h25',h21',h22',h27',h28']

theorem full_spec (s : Fin 35 → List Bool) (a b : ℚ)
    (hc : ∀ i, i.val < 16 → s i = [])
    (ha : s 19 = KS.W01.encodeRat a) (hb : s 20 = KS.W01.encodeRat b)
    (h21 : s 21 = []) (h22 : s 22 = []) (h24 : s 24 = []) (h25 : s 25 = [])
    (h27 : s 27 = []) (h28 : s 28 = []) :
    RunSpec program s (result s a b) (ticks s a b) := by
  have h := arithmetic_spec s a b hc ha hb h21 h22 h24 h25 h27 h28
  have hclean := KS.W04.CleanRationalCompare.clearList_spec (28 : Fin 35) cleanupPorts (after s a b)
  have he : KS.W04.CleanRationalCompare.clearListState cleanupPorts (after s a b) = result s a b := by
    funext i
    fin_cases i <;> simp [result,cleanupPorts,after,put,
      KS.W04.CleanRationalCompare.clearListState,KS.W04.CleanRationalCompare.clearState]
  rw [he] at hclean
  exact h.compose hclean

end KS.W19.SparseCoefficientStage

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_TerminalWitnessMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07 Matrix

theorem scalar_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    RunSpec SparseCoefficientStage.program (collected saved M j)
      (Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j)))
      (scalarTicks saved M j) := by
  have hc : ∀ i : Fin 35, i.val < 16 → collected saved M j i = [] := by
    intro i hi; fin_cases i <;> simp_all [collected,inputState]
  have h := SparseCoefficientStage.full_spec (collected saved M j)
    (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)
    hc rfl rfl rfl rfl rfl rfl rfl rfl
  have he : SparseCoefficientStage.result (collected saved M j)
      (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j) =
      Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j)) := by
    funext i
    fin_cases i <;> simp [SparseCoefficientStage.result,SparseCoefficientStage.cleanupPorts,
      KS.W04.CleanRationalCompare.clearListState,KS.W04.CleanRationalCompare.clearState,
      collected,inputState,coefficient]
  rw [he] at h
  exact h

theorem full_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (j : Fin (n+1)) (hj : j ≠ 0) :
    RunSpec program (inputState saved M j) (outputState saved M j) (ticks saved M B j) := by
  have h1 := collect_spec saved M B hnum hden j
  have h2 := scalar_spec saved M j
  have h3 := TerminalSparseAssembly.sparse_spec
    (Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j))) j hj (coefficient M j)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have he : Function.update (Function.update (Function.update
      (Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j))) 28 []) 30 []) 23
        (KS.W12.RowDot.vectorTape (TerminalVectorReplace.sparseVector j (coefficient M j))) =
      outputState saved M j := by
    funext i
    fin_cases i <;> simp [outputState,inputState,coefficient,SparseScalarNodes.coefficient,
      TerminalVectorReplace.sparseVector,KS.W17.zeroPivotWitness]
  rw [he] at h3
  exact h1.compose (h2.compose h3)

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotTerminalMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem sparseTerminal_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n) :
    RunSpec sparseTerminal
      (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true])
      (terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
      (2+KS.W19.TerminalWitnessMachine.ticks saved M b j.succ) := by
  have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 35)
    (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true])
  have he : KS.W04.CleanRationalCompare.clearState 29
      (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true]) =
      KS.W19.TerminalWitnessMachine.inputState saved M j.succ := by
    funext k; fin_cases k <;> simp [KS.W04.CleanRationalCompare.clearState,
      KS.W19.TerminalWitnessMachine.inputState,Function.update]
  rw [he] at hc
  have hs := KS.W19.TerminalWitnessMachine.full_spec saved M b hnum hden j.succ (Fin.succ_ne_zero j)
  have ho : KS.W19.TerminalWitnessMachine.outputState saved M j.succ =
      terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ) := by
    funext k; fin_cases k <;> simp [KS.W19.TerminalWitnessMachine.outputState,
      terminalState,matrixState,state,Function.update]
  rw [ho] at hs
  exact hc.compose hs

theorem terminal_sparse_case {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n) :
    RunSpec terminalProgram
      (Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true])
      (terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
      ((2+KS.W19.TerminalWitnessMachine.ticks saved M b j.succ)+1) := by
  apply KS.W06.RationalCompare.branch_spec_right unitTerminal sparseTerminal 23 terminalSelect
    _ _ _ _ (sparseTerminal_spec saved M b hnum hden j)
  intro coin
  simp [terminalSelect,observedHeads,KS.W29.topCode,Function.update,KS.W06.RationalCompare.stayActions]

theorem terminal_sparse_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n)
    (hz : DenseRatMatrix.decode M 0 0 = 0)
    (hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    RunSpec terminalProgram (withSaved saved (PivotDecision.result M))
      (terminalState saved M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
      ((2+KS.W19.TerminalWitnessMachine.ticks saved M b j.succ)+1) := by
  rw [PivotDecision.result_sparse M j hz hj]
  have he : withSaved saved (PivotRowLoop.finished M j.succ.val true) =
      Function.update (KS.W19.TerminalWitnessMachine.inputState saved M j.succ) 29 [true] := by
    funext k; fin_cases k <;> simp [withSaved,PivotRowLoop.finished,
      KS.W19.TerminalWitnessMachine.inputState,Function.update]
  rw [he]
  exact terminal_sparse_case saved M b hnum hden j

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotControllerBody
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem body_sparse_spec {n N : ℕ} (h : PivotHistory (n+1) N) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) (j : Fin n)
    (hz : DenseRatMatrix.decode M 0 0 = 0)
    (hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    RunSpec controllerBody (matrixState (historyTape h) M)
      (state [] [] [] [] (KS.W12.RowDot.vectorTape
        (h.restore (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))))
      (PivotDecision.ticks M b+
        (((2+KS.W19.TerminalWitnessMachine.ticks (historyTape h) M b j.succ)+1+
          finishTicks h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))+1)) := by
  have ht := (terminal_sparse_spec (historyTape h) M b hnum hden j hz hj).compose
    (finishTerminal_spec h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))
  have hs : ∀ coin, afterDecisionSelect (observedHeads
      (⟨some (KS.W29.FixedBranch.start fullDescendProgram terminalRestoreProgram),
        withSaved (historyTape h) (PivotDecision.result M)⟩ :
        Config 35 (fullDescendProgram.states+terminalRestoreProgram.states+1))) coin =
      ⟨.right,KS.W06.RationalCompare.stayActions 35⟩ := by
    intro coin
    rw [PivotDecision.result_sparse M j hz hj]
    simp [afterDecisionSelect,withSaved,PivotRowLoop.finished,observedHeads,KS.W29.topCode,
      KS.W06.RationalCompare.stayActions]
  have hb := KS.W06.RationalCompare.branch_spec_right fullDescendProgram terminalRestoreProgram 23
    afterDecisionSelect _ _ _ hs ht
  exact (decision_spec (historyTape h) M b hnum hden).compose hb

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotControllerCorrectness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem run_controller {n N : ℕ} (h : PivotHistory n N) (M : DenseRatMatrix n)
    (bits : List Bool) (hlen : controllerTicks h M ≤ bits.length) :
    controllerProgram.toMachine.run (controllerConfig (matrixState (historyTape h) M)) bits =
      ⟨none,witnessState ((uniformNegativeWitness n (DenseRatMatrix.decode M)).map h.restore)⟩ := by
  induction n generalizing N bits with
  | zero =>
    have hclear := controller_run_clear (historyTape h) bits hlen
    simp [matrixState,uniformNegativeWitness,witnessState,
      KS.W08.denseMatrixTape,KS.W08.denseMatrixPayloads,Computability.encodeNat] at hclear ⊢
    exact hclear
  | succ n ih =>
    have hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^(localBits M) :=
      fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).1
    have hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^(localBits M) :=
      fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).2
    have hN : 0<N := by have hd := h.dimension_depth; omega
    have descend (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
        controllerProgram.toMachine.run (controllerConfig (matrixState (historyTape h) M)) bits =
          ⟨none,witnessState ((uniformNegativeWitness (n+1) (DenseRatMatrix.decode M)).map h.restore)⟩ := by
      have hb := body_descend_spec (historyTape h) M (localBits M) hnum hden ht
      have hbudget := controllerTicks_descend h M ht
      cases bits with
      | nil => simp only [List.length_nil] at hlen; rw [hbudget] at hlen; omega
      | cons coin bs =>
        have hbnd : PivotDecision.ticks M (localBits M)+(descentTicks M (localBits M)+1) ≤ bs.length := by
          rw [hbudget] at hlen
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then controllerGuard bs hbnd
        erw [Machine.run.eq_2,controller_step_call]
        change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.run _ bs = _
        erw [hreturn]
        have hremain : controllerTicks (.push (DenseRatMatrix.decode M) h) (child M) ≤ remaining.length := by
          rw [hbudget] at hlen
          simp only [List.length_cons] at hlen
          omega
        have hrec := ih (N:=N) (h:=PivotHistory.push (DenseRatMatrix.decode M) h)
          (M:=child M) (bits:=remaining) hremain
        simp [historyTape,DenseRatMatrix.ofMatrix_decode,uniformNegativeWitness,ht,
          witnessState,Option.map_map,Function.comp_def,PivotHistory.restore,child] at hrec ⊢
        exact hrec
    by_cases hn : DenseRatMatrix.decode M 0 0 < 0
    · have hb := body_negative_spec h M (localBits M) hnum hden hn
      cases bits with
      | nil => simp [controllerTicks,hn] at hlen
      | cons coin bs =>
        have hbnd : PivotDecision.ticks M (localBits M)+
            (((2+unitTicks n)+1+finishTicks h M (Pi.single 0 1))+1) ≤ bs.length := by
          simp only [controllerTicks,hn,ite_true, if_true,List.length_cons] at hlen
          omega
        obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then controllerGuard bs hbnd
        erw [Machine.run.eq_2,controller_step_call]
        change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.run _ bs = _
        erw [hreturn]
        have hremain : 1 ≤ remaining.length := by
          simp only [controllerTicks,hn,ite_true, if_true,List.length_cons] at hlen
          omega
        cases remaining with
        | nil => simp at hremain
        | cons c cs =>
          change controllerProgram.toMachine.run
            (controllerConfig (state [] [] [] []
              (KS.W12.RowDot.vectorTape (h.restore (Pi.single 0 1))))) (c :: cs) = _
          erw [Machine.run.eq_2,controller_step_finished _ (vectorTape_nonempty hN _),Machine.run_halted _ _ rfl]
          simp [witnessState,uniformNegativeWitness,pivotTerminal,hn]
    · by_cases hz : DenseRatMatrix.decode M 0 0 = 0
      · cases hf : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) with
        | none => exact descend (by simp [pivotTerminal,hz,hf])
        | some j =>
          have hb := body_sparse_spec h M (localBits M) hnum hden j hz hf
          cases bits with
          | nil => simp [controllerTicks,hz,hf] at hlen
          | cons coin bs =>
            have hbnd : PivotDecision.ticks M (localBits M)+
                (((2+KS.W19.TerminalWitnessMachine.ticks (historyTape h) M (localBits M) j.succ)+1+
                  finishTicks h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))+1) ≤ bs.length := by
              simp only [controllerTicks,hz,lt_self_iff_false,ite_true, if_true,ite_false, if_false,hf,List.length_cons] at hlen
              omega
            obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then controllerGuard bs hbnd
            erw [Machine.run.eq_2,controller_step_call]
            change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.run _ bs = _
            erw [hreturn]
            have hremain : 1 ≤ remaining.length := by
              simp only [controllerTicks,hz,lt_self_iff_false,ite_true, if_true,ite_false, if_false,hf,List.length_cons] at hlen
              omega
            cases remaining with
            | nil => simp at hremain
            | cons c cs =>
              change controllerProgram.toMachine.run
                (controllerConfig (state [] [] [] []
                  (KS.W12.RowDot.vectorTape
                    (h.restore (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ)))))
                (c :: cs) = _
              erw [Machine.run.eq_2,controller_step_finished _ (vectorTape_nonempty hN _),Machine.run_halted _ _ rfl]
              simp [witnessState,uniformNegativeWitness,pivotTerminal,hz,hf]
      · exact descend (by simp [pivotTerminal,hn,hz])

theorem controller_spec (n : ℕ) (M : DenseRatMatrix n) :
    RunSpec controllerProgram (matrixState [] M)
      (witnessState (rationalNegativeWitness n (DenseRatMatrix.decode M)))
      (controllerTicks (.nil n) M) := by
  intro bits hb
  have h := run_controller (.nil n) M bits hb.ge
  simp [historyTape,PivotHistory.restore,uniformNegativeWitness_eq] at h ⊢
  exact h

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerRuntime
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem controller_original_spec {N : ℕ} (A : DenseRatMatrix N) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    RunSpec controllerProgram (matrixState [] A)
      (witnessState (rationalNegativeWitness N (DenseRatMatrix.decode A))) (originalControllerBound N b) :=
  (controller_spec N A).mono (ControllerReachable.controller_ticks_le ControllerReachable.initial b hnum hden)

theorem controller_payload_spec {N : ℕ} (A : DenseRatMatrix N) :
    RunSpec controllerProgram (matrixState [] A)
      (witnessState (rationalNegativeWitness N (DenseRatMatrix.decode A)))
      (originalControllerBound N (localBits A)) :=
  controller_original_spec A (localBits A)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload A i j).1)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload A i j).2)

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PSDControllerPolynomial
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PSDControllerPolynomial
open KS.W07 KS.W17 KS.W17.FixedPSD KS.W03.MachineCombinators

theorem controller_polynomial_spec {N : ℕ} (A : DenseRatMatrix N) :
    RunSpec controllerProgram (matrixState [] A)
      (witnessState (rationalNegativeWitness N (DenseRatMatrix.decode A)))
      (KS.W29.polynomialFuel coefficient 58 (KS.W08.denseMatrixTape A).length) :=
  (controller_payload_spec A).mono
    (originalControllerBound_le_monomial (KS.W19.TerminalWitnessMachine.dimension_le_payload A))

end KS.W23.PSDControllerPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PSDCleanRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.PSDCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07 KS.W17 KS.W17.FixedPSD
open CleanRoutine

lemma program_spec (a : Datum) : RunSpec program (io (input a)) (io (output a)) (ticks a) := by
  have h := (decode_spec a).compose ((install_spec a).compose
    ((KS.W23.PSDControllerPolynomial.controller_polynomial_spec a.2).compose
      (extract_spec (rationalNegativeWitness a.1 (DenseRatMatrix.decode a.2)))))
  simp only [ticks,output,Nat.add_assoc] at h ⊢
  exact h

def routine : Routine input output ticks where
  scratch := 34
  program := program
  spec := program_spec

end CurrentKS.PSDCleanRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StoredPSDRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

def psdStored : Realizes matrixObjectCode vectorCode witnessData := by
  let gen := (first natCode matrixCode).then natToBinary
  let flat := (second natCode matrixCode).then (flattenList ratCode)
  let prep := (gen.both flat).reindex matrixObjectCode (fun a => (a.1,matrixData a.2)) (fun _ => rfl)
  let pre := prep.changeOutput PSDCleanRoutine.input
    (fun a : MatrixObject => ⟨a.1,KS.W07.DenseRatMatrix.ofMatrix a.2⟩) (by
      intro a
      change KS.W01.frame (Computability.encodeNat a.1)++vectorCode (matrixData a.2).flatten=_
      rw [matrixData_tape]
      rfl)
  let raw : Realizes PSDCleanRoutine.input vectorCode
      (fun a => (KS.W17.rationalNegativeWitness a.1 (KS.W07.DenseRatMatrix.decode a.2)).elim [] List.ofFn) := {
    cost := PSDCleanRoutine.ticks
    routine := {
      scratch := PSDCleanRoutine.routine.scratch
      program := PSDCleanRoutine.routine.program
      spec := fun a => by
        have h := PSDCleanRoutine.routine.spec a
        cases he : KS.W17.rationalNegativeWitness a.1 (KS.W07.DenseRatMatrix.decode a.2) with
        | none =>
          simp only [PSDCleanRoutine.output,he,Option.elim_none] at h ⊢
          exact h
        | some v =>
          simpa only [PSDCleanRoutine.output,he,Option.elim_some,vector_tape] using h } }
  exact (pre.then raw).congr (fun a => by simp only [witnessData,KS.W07.DenseRatMatrix.decode_ofMatrix])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoundedStepRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

def stateWitness : Realizes pencilStateCode vectorCode
    (fun s => (s.B.witness s.y).elim [] List.ofFn) := by
  let evaluation := (statePencil.both stateY).then evalPencil
  let dim := statePencil.then ((first matrixCode (listCode matrixCode)).then (lengthList vectorCode))
  let prep := (dim.both evaluation).changeOutput matrixObjectCode
    (fun s : PencilState => ⟨s.m,s.B.eval s.y⟩) (by
      intro s
      change prodCode natCode matrixCode ((matrixData s.B.constant).length,
        evalPencilData (pencilData s.B,List.ofFn s.y))=_
      rw [evalPencil_data]
      simp only [matrixData,List.length_ofFn,matrixObjectCode])
  exact prep.then psdStored

def stateNextVector : Realizes pencilStateCode vectorCode
    (fun s => List.ofFn (s.B.next s.step s.mesh s.y)) := by
  let witness := stateWitness
  let isNone := witness.then ((lengthList ratCode).then natIsZero)
  let normal := (statePencil.both witness).then normalPencil
  let moved := (stateParameters.both (stateY.both normal)).then roundedUpdate
  refine (isNone.ite stateY moved).congr ?_
  intro s
  change (if decide (((s.B.witness s.y).elim [] List.ofFn).length=0) then List.ofFn s.y else
    roundedUpdateValue ((s.step,s.mesh),(List.ofFn s.y,
      normalData (pencilData s.B,(s.B.witness s.y).elim [] List.ofFn))))=_
  cases hw : s.B.witness s.y with
  | none => simp [RationalSDP.Pencil.next,hw]
  | some v =>
    have hm := nonempty_witness_dimension (s.B.eval s.y) v hw
    simp only [Option.elim_some,List.length_ofFn,hm,decide_false,Bool.false_eq_true,↓reduceIte,
      normalPencil_data,roundedUpdate_ofFn,RationalSDP.Pencil.next,hw]

def pencilNext : Realizes pencilStateCode pencilStateCode PencilState.next :=
  (statePencil.both (stateParameters.both stateNextVector)).changeOutput pencilStateCode
    PencilState.next (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def search : Realizes searchStateCode vectorCode
    (fun s => List.ofFn (s.B.search s.r s.R s.y)) :=
  (((searchFuelRealizes.both searchInit).then pencilNext.iterate).then stateY).congr (by
    intro s
    exact congrArg (fun t : PencilState => List.ofFn t.y)
      (pencilNext_iterate s.init (RationalSDP.searchFuel s.n s.r s.R)))

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_WitnessRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def isPSD : Realizes matrixObjectCode boolCode
    (fun a : MatrixObject => decide (KS.W17.rationalNegativeWitness a.1 a.2=none)) :=
  ((psdStored.then (lengthList ratCode)).then natIsZero).congr (by
    intro a
    unfold witnessData
    cases hw : KS.W17.rationalNegativeWitness a.1 a.2 with
    | none => rfl
    | some v =>
      have hn := nonempty_witness_dimension a.2 v hw
      simp [hn])

def witnessNone : Realizes witnessStateCode boolCode (fun a => decide (a.B.witness a.y=none)) :=
  witnessEvaluation.then isPSD

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OptimizeRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def optCandidate : Realizes (prodCode optCode natCode) vectorCode
    (fun p => List.ofFn (p.1.B.levelCandidate p.1.f p.1.delta p.1.r p.1.R p.1.U p.2)) :=
  let p := first optCode natCode
  let zero := ((constant (prodCode optCode natCode) ratCode 0).both
    ((p.then optF).then (lengthList ratCode))).then (replicateList ratCode)
  let prep := (optLevelPencil.both ((p.then optRadius).both zero)).changeOutput
    searchStateCode candidateSearch (by
      intro p
      simp only [List.length_ofFn,searchStateCode,searchStateData,candidateSearch,
        pencilStateDataCode,Pi.zero_def,List.ofFn_const])
  prep.then search

def osFeasible : Realizes optStateCode boolCode
    (fun s => decide ((s.p.B.withLevel s.p.f (RationalSDP.level s.p.delta s.p.U s.k)).witness s.y=none)) :=
  ((((osP.both osK).then optLevelPencil).both osY).changeOutput witnessStateCode
    OptState.feasibility (fun _ => rfl)).then witnessNone

def osNext : Realizes optStateCode optStateCode OptState.next :=
  let nextY := osFeasible.ite osY ((osP.both (osK.then natSucc)).then optCandidate)
  (osP.both ((osK.then natSucc).both nextY)).changeOutput optStateCode OptState.next (by
    intro s
    unfold optStateCode optStateData OptState.next
    split_ifs <;> simp_all [optStateDataCode])

def optInit : Realizes optCode optStateCode OptParams.init :=
  let cand := ((identity optCode).both (constant optCode natCode 0)).then optCandidate
  ((identity optCode).both ((constant optCode natCode 0).both cand)).changeOutput optStateCode
    OptParams.init (fun _ => rfl)

def optimize : Realizes (prodCode optCode natCode) vectorCode
    (fun p => List.ofFn (p.1.B.optimize p.1.f p.1.delta p.1.r p.1.R p.1.U p.2)) :=
  let init := (first optCode natCode).then optInit
  let k := second optCode natCode
  (((k.both init).then osNext.iterate).then osY).congr (by
    intro p
    exact congrArg (fun s : OptState => List.ofFn s.y) (opt_iterate p.1 p.2))

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueQueryRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def vqFuel : Realizes valueQueryCode natCode (fun p => RationalSDP.optimizeFuel p.delta 100) :=
  let q := (constant valueQueryCode ratCode 200).div vqDelta
  (((q.then ratCeil).both (constant valueQueryCode natCode 3)).then natAdd).congr (by
    intro p
    simp only [RationalSDP.optimizeFuel]
    norm_num)

def valueQueryPoint : Realizes valueQueryCode vectorCode
    (fun p => List.ofFn (RationalSDP.valueQueryPoint p.coords p.x p.theta p.nu p.delta)) :=
  (vqOpt.both vqFuel).then optimize

def valueQuery : Realizes valueQueryCode ratCode
    (fun p => RationalSDP.valueQuery p.coords p.x p.theta p.nu p.delta) :=
  ((vqData.both valueQueryPoint).then valueObjective).congr (by
    intro p
    exact valueObjective_data p.coords p.x p.theta (p.nu/p.d) _)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PotentialRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def potentialQuery : Realizes potentialCode ratCode
    (fun p => RationalSDP.potentialQuery p.coords p.x p.nu p.lam p.error) :=
  ((ppQuery.then valueQuery).add (ppLam.mul (ppTheta.then sumRationals))).congr (by
    intro p
    simp only [List.sum_ofFn]
    rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScheduleRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*} {ea : α → Word} {f g : α → ℚ}

def saCoarse : Realizes scheduleArgsCode ratCode
    (fun p => Schedule.coarseBudgetQ p.1 p.2.1 (p.2.2.1/(p.1:ℚ)) (p.2.2.2^2/p.2.2.1)) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let d := (saD.then natToRat).add (c 1)
  let n := saN.then natToRat
  ((((((c 200).add d).add saEpsilon.abs).add (((c 200).div saEpsilon).mul d)).add ((c 200).mul d)).add
    (d.add n)).add ((((c 384).mul n).mul ((c 1).add ((c 800).div (saSigma.pow 3)))))

def saCurve2 : Realizes scheduleArgsCode ratCode
    (fun p => Schedule.valueCurve2Q p.1 p.2.1 (p.2.2.1/(p.1:ℚ)) (p.2.2.2^2/p.2.2.1)) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let d := (saD.then natToRat).add (c 1)
  let J := ((c (10^18)).mul d).mul (((c 1).add saEpsilon.inv).pow 4)
  let D := (c 300).mul (saCoarse.pow 5)
  ((c 1).add (saEpsilon.abs.mul ((c 2).mul d))).mul ((J.mul D).mul (((c 1).add (J.mul D)).pow 2))

def saCurve3 : Realizes scheduleArgsCode ratCode
    (fun p => Schedule.valueCurve3Q p.1 p.2.1 (p.2.2.1/(p.1:ℚ)) (p.2.2.2^2/p.2.2.1)) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let d := (saD.then natToRat).add (c 1)
  let J := ((c (10^18)).mul d).mul (((c 1).add saEpsilon.inv).pow 4)
  let D := (c 300).mul (saCoarse.pow 5)
  let JD := J.mul D
  let plus := (c 1).add JD
  ((c 1).add (saEpsilon.abs.mul ((c 2).mul d))).mul
    (JD.mul ((plus.pow 3).add (((c 3).mul plus).mul (JD.mul (plus.pow 2)))))

def saBudget :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  (((c 1).add saCurve2).add saCurve3).add
    ((saLam.abs.mul (saN.then natToRat)).mul ((c 1).add ((c 800).div (saSigma.pow 3))))
def saStep :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  (saSigma.div (c 4)).min ((saThreshold.div ((c 4).mul saBudget)).min (c (1/4)))
def saStencil :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  (saSigma.div (c 8)).min ((c 1).min (saThreshold.div (((c 64).mul saBudget).mul (saN.then natToRat))))
def saMesh :=
  (saStep.mul saThreshold).div
    (((constant scheduleArgsCode ratCode 4096).mul saBudget).mul (saN.then natToRat))

def parameters : Realizes scheduleArgsCode parametersCode
    (fun p => Schedule.parameters p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let stencilErr := (saThreshold.mul (saStencil.pow 2)).div ((c 128).mul (saN.then natToRat))
  let selectionErr := (saThreshold.mul (saStep.pow 2)).div (c 4)
  let push {f : ℕ×(ℕ×(ℚ×ℚ)) → ℚ} {g : ℕ×(ℕ×(ℚ×ℚ)) → List ℚ}
      (r : Realizes scheduleArgsCode ratCode f) (s : Realizes scheduleArgsCode vectorCode g) :=
    (r.both s).then (consList ratCode)
  (push saEpsilon (push saSigma (push saThreshold (push saBudget (push saStep
    (push saStencil (push saMesh (push stencilErr (selectionErr.then (singletonRat)))))))))).changeOutput
    parametersCode (fun p => Schedule.parameters p.1 p.2.1 p.2.2.1 p.2.2.2) (fun _ => rfl)
where
  singletonRat : Realizes ratCode vectorCode (fun q => [q]) :=
    ((identity ratCode).both (constant ratCode vectorCode [])).then (consList ratCode)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceQueryRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def fSchedule : Realizes faceCode parametersCode FaceParams.schedule :=
  (fD.both (fN.both fScalars)).then parameters

def faceQuery : Realizes (prodCode facePointCode ratCode) ratCode
    (fun q => RationalSDP.faceQuery q.1.p.coords q.1.p.base q.1.y q.1.p.nu q.1.p.lam q.2) :=
  fpPotential.then potentialQuery

def faceStencil : Realizes facePointCode ratCode
    (fun q => RationalFace.faceStencil q.p.coords q.p.base q.p.nu q.p.lam q.y) :=
  let err := (fpP.then fSchedule).then (parameterField 7)
  ((identity facePointCode).both err).then faceQuery

def faceScore : Realizes facePointCode ratCode
    (fun q => RationalFace.faceScore q.p.coords q.p.base q.p.nu q.p.lam q.y) :=
  let err := (fpP.then fSchedule).then (parameterField 8)
  ((identity facePointCode).both err).then faceQuery

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StencilRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*}

def stencilAt {ea : α → Word} (p : α → FaceParams) (pr : Realizes ea faceCode p)
    (v : (a : α) → Fin (p a).n → ℚ) (vr : Realizes ea vectorCode (fun a => List.ofFn (v a))) :
    Realizes ea ratCode (fun a => Difference.stencilValue
      (RationalFace.faceStencil (p a).coords (p a).base (p a).nu (p a).lam)
      (RationalFace.faceState (p a).base) (p a).schedule.h (v a)) :=
  let h : Realizes ea ratCode (fun a => (p a).schedule.h) := (pr.then fSchedule).then (parameterField 5)
  let y := ((pr.then fState).both ((h.both vr).then vectorScale)).then vectorAdd
  let point := (pr.both y).changeOutput facePointCode
    (fun a => ⟨p a,fun i => RationalFace.faceState (p a).base i+(p a).schedule.h*v a i⟩) (by
      intro a
      simp only [vectorScale_ofFn]
      change prodCode faceCode vectorCode (p a,zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0
        (List.ofFn (show Fin (p a).n → ℚ from RationalFace.faceState (p a).base),List.ofFn ((p a).schedule.h • v a)))=_
      rw [vectorAdd_ofFn]
      rfl)
  point.then faceStencil

def stencilGradientEntry : Realizes faceIndexCode ratCode
    (fun s => Difference.stencilGradient (RationalFace.faceStencil s.1.coords s.1.base s.1.nu s.1.lam)
      (RationalFace.faceState s.1.base) s.1.schedule.h s.2) :=
  let plus := stencilAt (fun s : FaceIndex => s.1) fiP (fun s => Difference.rationalBasis s.2) fiBasis
  let minus := stencilAt (fun s : FaceIndex => s.1) fiP (fun s => -Difference.rationalBasis s.2)
    ((fiBasis.then vectorNeg).congr (fun _ => vectorNeg_ofFn _))
  (plus.sub minus).div ((constant faceIndexCode ratCode 2).mul ((fiP.then fSchedule).then (parameterField 5)))

def stencilGradient : Realizes faceCode vectorCode
    (fun p => List.ofFn (Difference.stencilGradient
      (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h)) :=
  stencilGradientEntry.tabulateFin fN

def stencilHessianEntry : Realizes faceDoubleCode ratCode
    (fun s => Difference.stencilHessian
      (RationalFace.faceStencil s.1.1.coords s.1.1.base s.1.1.nu s.1.1.lam)
      (RationalFace.faceState s.1.1.base) s.1.1.schedule.h s.1.2 s.2) :=
  let c (q : ℚ) := constant faceDoubleCode ratCode q
  let h : Realizes faceDoubleCode ratCode (fun s => s.1.1.schedule.h) := (fdP.then fSchedule).then (parameterField 5)
  let value := ((fdP.both (fdP.then fState)).changeOutput facePointCode
    (fun s => ⟨s.1.1,RationalFace.faceState s.1.1.base⟩) (fun _ => rfl)).then faceStencil
  let bi := fdBasisI
  let bj := fdBasisJ
  let nbi := (bi.then vectorNeg).congr (fun s => vectorNeg_ofFn _)
  let nbj := (bj.then vectorNeg).congr (fun s => vectorNeg_ofFn _)
  let query (v : (s : FaceDouble) → Fin s.1.1.n → ℚ)
      (vr : Realizes faceDoubleCode vectorCode (fun s => List.ofFn (v s))) :=
    stencilAt (fun s : FaceDouble => s.1.1) fdP v vr
  let plus := query (fun s => Difference.rationalBasis s.1.2) bi
  let minus := query (fun s => -Difference.rationalBasis s.1.2) nbi
  let add (v w : (s : FaceDouble) → Fin s.1.1.n → ℚ)
      (vr : Realizes faceDoubleCode vectorCode (fun s => List.ofFn (v s)))
      (wr : Realizes faceDoubleCode vectorCode (fun s => List.ofFn (w s))) :=
    (vr.both wr).then vectorAdd |>.congr (fun s => vectorAdd_ofFn _ _)
  let pp := query _ (add _ _ bi bj)
  let pm := query _ (add _ _ bi nbj)
  let mp := query _ (add _ _ nbi bj)
  let mm := query _ (add _ _ nbi nbj)
  let diag := ((plus.sub ((c 2).mul value)).add minus).div (h.pow 2)
  let off := (((pp.sub pm).sub mp).add mm).div ((c 4).mul (h.pow 2))
  (((fdI.both fdJ).then natEq).ite diag off).congr (by
    intro s
    simp only [Difference.stencilHessian,decide_eq_true_eq,sub_eq_add_neg]
    by_cases hij : s.1.2=s.2
    · simp only [hij,ite_true, if_true]
    · have hv : s.1.2.val≠s.2.val := fun hh => hij (Fin.ext hh)
      simp only [hij,hv,ite_false, if_false])

def stencilHessianRow := stencilHessianEntry.tabulateFin (fiP.then fN)
def stencilHessian : Realizes faceCode matrixCode
    (fun p => matrixData (Difference.stencilHessian
      (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h)) :=
  stencilHessianRow.tabulateFin fN

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CurvatureRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def computedCurvature : Realizes curvatureCode vectorCode
    (fun p => (RationalRoot.computedCurvature p.H p.a p.M p.s p.rho).elim [] List.ofFn) :=
  let c (q : ℚ) := constant curvatureCode ratCode q
  let v := cuShift.then psdStored
  let beta := cuA.div ((c 4096).mul cuM)
  let w := ((beta.both v).then normalizeVector)
  let factor := cuS.mul ((c 1).sub (cuA.div ((c 1024).mul cuM)))
  let scaled := (factor.both w).then vectorScale
  ((cuRho.both scaled).then roundMesh).congr (by
    intro p
    unfold RationalRoot.computedCurvature RationalRoot.negativeDirection
    cases hh : KS.W17.rationalNegativeWitness p.n (RationalRoot.shiftedHessian p.H p.a) with
    | none => simp [witnessData,hh,normalizeData,initialScaleData]
    | some v =>
      simp only [witnessData,hh,Option.elim_some,Option.map_some,normalize_data,vectorScale_ofFn,roundMesh_data]
      rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceChoiceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def faceCurvatureParams : Realizes faceCode curvatureCode FaceParams.curvatureParams :=
  let sp := fSchedule
  (fN.both (stencilHessian.both ((sp.then (parameterField 2)).both
    ((sp.then (parameterField 3)).both ((sp.then (parameterField 4)).both (sp.then (parameterField 6))))))).changeOutput
    curvatureCode FaceParams.curvatureParams (fun _ => rfl)
def faceCurvature : Realizes faceCode vectorCode (fun p => p.curvature.elim [] List.ofFn) :=
  faceCurvatureParams.then computedCurvature

def faGradientPoint : Realizes activeFaceCode vectorCode (fun p => List.ofFn p.gradientPoint) :=
  let x := faP.then fState
  let step := (faP.then fSchedule).then (parameterField 4)
  let g := (faP.then stencilGradient).then gradientDirection
  ((x.both ((step.both g).then vectorScale)).then vectorAdd).congr (by
    intro p
    let : NeZero p.val.n := ⟨p.property⟩
    change zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0
      (List.ofFn (RationalFace.faceState p.val.base),
        (gradientDirectionData (List.ofFn p.val.gradient)).map (fun q => p.val.schedule.s*q))=_
    rw [gradientDirection_data,vectorScale_ofFn,vectorAdd_ofFn]
    rfl)

def faCandidates : Realizes activeFaceCode (listCode vectorCode)
    (fun p => p.candidates.map List.ofFn) :=
  let endpoints := (faP.then fState).then endpointCandidates
  let curves := (((faP.then fState).both (faP.then faceCurvature)).then curvatureCandidates)
  let inside := (faGradientPoint.both curves).then (consList vectorCode)
  ((endpoints.both inside).then (appendList vectorCode)).congr (by
    intro p
    let : NeZero p.val.n := ⟨p.property⟩
    change endpointData (List.ofFn (RationalFace.faceState p.val.base))++
      (List.ofFn p.gradientPoint::curvatureCandidatesData
        (List.ofFn (RationalFace.faceState p.val.base),p.val.curvature.elim [] List.ofFn))=_
    rw [endpoint_data,curvatureCandidates_data]
    simp only [FaceActive.candidates,RationalFace.faceCandidates,Difference.allCandidates,
      Difference.interiorCandidates,List.map_append,List.map_cons,FaceActive.gradientPoint,
      FaceParams.gradient,FaceParams.hessian,FaceParams.curvature,FaceParams.schedule]
    rfl)

def faCandidatePoints : Realizes activeFaceCode (listCode facePointCode)
    (fun p => p.candidates.map (fun y => (⟨p.val,y⟩ : FacePoint))) :=
  (((faP.both faCandidates).then (identity (prodCode faceCode vectorCode)).mapCtx)).changeOutput
    (listCode facePointCode) (fun p => p.candidates.map (fun y => (⟨p.val,y⟩ : FacePoint))) (by
      intro p
      simp only [listCode,FramedMapRoutine.tape,List.flatMap_map,List.map_map,Function.comp_def,id_eq]
      rfl)

def faChoice : Realizes activeFaceCode vectorCode (fun p => List.ofFn p.choice) :=
  let defaultPoint := ((faP.both (faP.then fState)).changeOutput facePointCode
    (fun p => ⟨p.val,RationalFace.faceState p.val.base⟩) (fun _ => rfl))
  let scored := fpY.both faceScore
  let init := defaultPoint.then scored
  let all := faCandidatePoints.then scored.map
  (((init.both all).then (selectScored vectorCode)).then (first vectorCode ratCode)).congr (by
    intro p
    have h := selectScored_data (RationalFace.faceScore p.val.coords p.val.base p.val.nu p.val.lam)
      List.ofFn p.candidates (RationalFace.faceState p.val.base)
    simpa only [List.map_map,Function.comp_def,FaceActive.choice,RationalFace.faceChoice,FaceActive.candidates] using congrArg Prod.fst h)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceRunRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def faNextBase : Realizes activeFaceCode vectorCode (fun p => List.ofFn p.nextBase) :=
  let point := (faP.both faChoice).changeOutput facePointCode (fun p => ⟨p.val,p.choice⟩) (fun _ => rfl)
  let sigma := ((faP.then fLam).pow 2).div (faP.then fNu)
  ((sigma.both (point.then fpExtend)).then freezeVector).congr (fun _ => freezeVector_data _ _)

def faceNext : Realizes faceCode faceCode FaceParams.next :=
  let test := (fN.then natIsZero).congr (fun _ => rfl)
  let stop := (identity faceCode).reindex (fun p : {p : FaceParams // p.n=0} => faceCode p.val) Subtype.val (fun _ => rfl)
  let advance := packFace faP faNextBase
  (test.dite stop advance).congr (by
    intro p
    by_cases hn : p.n=0
    · simp only [hn,dite_eq_left,FaceParams.next,RationalFace.transition, id_eq,Option.getD_none]
    · simp only [hn,FaceParams.next,RationalFace.transition]
      rfl)

def fUniformDrop : Realizes faceCode ratCode
    (fun p => RationalFace.uniformDrop p.d p.N p.nu p.lam) :=
  let p := first faceCode natCode
  let n := second faceCode natCode
  let args := (p.then fD).both (n.both (p.then fScalars))
  let schedule := args.then parameters
  let drop := (schedule.then (parameterField 2)).mul ((schedule.then (parameterField 4)).pow 2)
  let count := ((fBase.then (lengthList ratCode)).then natSucc)
  ((((identity faceCode).both count).then drop.tabulate).then minList).congr (by
    intro p
    simp only [List.length_ofFn,id_eq]
    rfl)
def fFuel : Realizes faceCode natCode
    (fun p => Descent.fuel (RationalFace.uniformDrop p.d p.N p.nu p.lam)) :=
  (((constant faceCode ratCode 100).div fUniformDrop).then ratCeil).then natSucc

def faceRun : Realizes faceCode vectorCode
    (fun p => List.ofFn (RationalFace.rationalRun p.coords p.nu p.lam)) :=
  (((fFuel.both faceStart).then faceNext.iterate).then fBase).congr (by
    intro p
    rw [next_iterate]
    rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VarianceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def mgTest : Realizes (prodCode matrixGridCode ratCode) boolCode (fun p => p.1.test p.2) :=
  (mgShift.then isPSD).congr (by
    intro p
    unfold MatrixGrid.test
    cases KS.W17.rationalNegativeWitness p.1.n (p.2 • 1-p.1.M) <;> rfl)

def gridStep : Realizes gridStateCode gridStateCode gridStepData :=
  let p := first matrixGridCode (prodCode natCode natCode)
  let args := second matrixGridCode (prodCode natCode natCode)
  let k := args.then (first natCode natCode)
  let prev := args.then (second natCode natCode)
  let q := (k.then natToRat).div ((p.then mgDen).then natToRat)
  let test := (p.both q).then mgTest
  p.both ((k.then natSucc).both (test.ite prev (k.then natSucc)))

def gridUpper : Realizes matrixGridCode ratCode (fun p => RationalGrid.upper p.den p.test) :=
  let init := (identity matrixGridCode).both (constant matrixGridCode (prodCode natCode natCode) (0,0))
  let run := ((mgDen.both init).then gridStep.iterate)
  let result := run.then ((second matrixGridCode (prodCode natCode natCode)).then (second natCode natCode))
  ((result.then natToRat).div (mgDen.then natToRat)).congr (by
    intro p
    rw [grid_iterate]
    rfl)

def fVarianceGrid : Realizes faceCode matrixGridCode
    (fun p => ⟨p.d+p.d,RationalSDP.rationalVariance p.coords,1000*p.N*p.d^2⟩) :=
  let den := ((((fBase.then (lengthList ratCode)).then natToRat).mul (constant faceCode ratCode 1000)).mul
    ((fD.then natToRat).pow 2)).then ratCeil
  (((fD.both fD).then natAdd).both (fVariance.both den)).changeOutput matrixGridCode
    (fun p => ⟨p.d+p.d,RationalSDP.rationalVariance p.coords,1000*p.N*p.d^2⟩) (by
      intro p
      simp only [List.length_ofFn,FaceParams.data]
      have h : ⌈(p.N:ℚ)*1000*(p.d:ℚ)^2⌉₊=1000*p.N*p.d^2 := by
        have he : (p.N:ℚ)*1000*(p.d:ℚ)^2=((1000*p.N*p.d^2:ℕ):ℚ) := by push_cast <;> ring
        rw [he,Nat.ceil_natCast]
      rw [h]
      rfl)
def varianceQuery : Realizes faceCode ratCode (fun p => RationalSDP.varianceQuery p.coords) :=
  fVarianceGrid.then gridUpper

def faceNormalized : Realizes faceCode faceCode
    (fun p => {p with nu := RationalSDP.varianceQuery p.coords, lam := Schedule.penaltyParameter p.N (RationalSDP.varianceQuery p.coords)}) :=
  let nu := varianceQuery
  let root := (nu.both nu).then upperSqrt
  let lam := root.div ((constant faceCode ratCode 200).mul ((fBase.then (lengthList ratCode)).then natToRat))
  (fD.both (fAtoms.both (fBase.both (nu.both lam)))).changeOutput faceCode
    (fun p => {p with nu := RationalSDP.varianceQuery p.coords, lam := Schedule.penaltyParameter p.N (RationalSDP.varianceQuery p.coords)}) (by
      intro p;simp only [List.length_ofFn];rfl)
def normalizedRun : Realizes faceCode vectorCode
    (fun p => List.ofFn (RationalFace.normalizedRun p.coords)) :=
  faceNormalized.then faceRun

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalSignRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def originalNormalizedSigns : Realizes originalCode vectorCode
    (fun x => List.ofFn (RationalFace.normalizedRun (RationalInput.normalizedCoordinates x))) :=
  originalFaceRealizes.then normalizedRun

def originalExtendedSigns : Realizes originalCode vectorCode
    (fun x => List.ofFn (RationalFace.extend (RationalInput.index x) (fun _ => 1)
      (RationalFace.normalizedRun (RationalInput.normalizedCoordinates x)))) :=
  let ones := ((constant originalCode ratCode 1).both originalN).then (replicateList ratCode)
  ((originalIndices.both (ones.both originalNormalizedSigns)).then extendVector).congr (by
    intro x
    rw [←List.ofFn_const,extendData_data])

def originalOutputBit : Realizes (finFamilyCode originalCode Input.N) boolCode
    (fun p => decide (RationalInput.orientation p.1 p.2*
      RationalFace.extend (RationalInput.index p.1) (fun _ => 1)
        (RationalFace.normalizedRun (RationalInput.normalizedCoordinates p.1)) p.2=1)) :=
  let x : Realizes (finFamilyCode originalCode Input.N) originalCode (fun p => p.1) := familyFirst
  let i : Realizes (finFamilyCode originalCode Input.N) natCode (fun p => p.2.val) := familyIndex
  let val := (i.both (x.then originalExtendedSigns)).then (getD ratCode 0)
  ((originalOrientation.mul val).eq (constant _ ratCode 1)).congr (by intro p;rw [getD_ofFn])

def originalSigningFramed : Realizes originalCode (listCode boolCode) RationalInput.signing :=
  let alltrue := ((constant originalCode boolCode true).both originalN).then (replicateList boolCode)
  let nontrivial := originalOutputBit.tabulateFin originalN
  (((originalCountRealizes.then natIsZero).ite alltrue nontrivial)).congr
    (by intro x;simp only [RationalInput.signing,decide_eq_true_eq])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix

def isHeavy : Realizes columnCode boolCode
    (fun x => (KS.W17.rationalNegativeWitness x.1.params.d
      (testMatrix x.1.params.q x.1.params.t x.1.params.v x.1.scales x.2)).isSome) :=
  ((testProgram.then isPSD).ite (constant columnCode boolCode false)
    (constant columnCode boolCode true)).congr (by
      intro x
      cases h : KS.W17.rationalNegativeWitness x.1.params.d
        (testMatrix x.1.params.q x.1.params.t x.1.params.v x.1.scales x.2) <;> simp)

def newScales : Realizes stateCode vectorCode
    (fun s => List.ofFn (advance s.params.q s.params.t s.params.v s.scales)) :=
  ((scales.both ((isHeavy.both updated).tabulateFin (params.then numColumns))).then
    (selectFlagged vectorCode)).congr (by
      intro s
      dsimp only
      rw [List.ofFn_eq_map (f := fun e =>
        ((KS.W17.rationalNegativeWitness s.params.d
          (testMatrix s.params.q s.params.t s.params.v s.scales e)).isSome,
          List.ofFn (Function.update s.scales e (s.params.t*s.scales e)))),find_map_flagged]
      unfold advance heavy
      cases h : (List.finRange s.params.m).find? (fun e =>
        (KS.W17.rationalNegativeWitness s.params.d
          (testMatrix s.params.q s.params.t s.params.v s.scales e)).isSome) <;> rfl)
def step : Realizes stateCode stateCode State.next :=
  (params.both newScales).changeOutput stateCode State.next (fun _ => rfl)

def run : Realizes (prodCode natCode paramsCode) vectorCode
    (fun a => List.ofFn (scalesAt a.2.q a.2.t a.2.v a.1)) :=
  ((((first natCode paramsCode).both ((second natCode paramsCode).then initial)).then
    step.iterate).then scales).congr (by
      intro a
      rw [next_iterate]
      rfl)

def normalized : Realizes fixedCode vectorCode
    (fun a => List.ofFn (normalizedScales a.1.q a.2 a.1.v)) :=
  (lengthProgram.both fixedStep).then run

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Search realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

def solvePencil : Realizes paramsCode vectorCode (fun p =>
    List.ofFn (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0)) :=
  initializeSearch.then CurrentKS.Realization.search

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Realization
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

def found : Realizes loopCode pointCode (fun a => ⟨a.params,a.vector⟩) :=
  ((loopParams.both (loopParams.then solvePencil)).then pointParser).congr
    (fun a => parsePoint_ofFn a.params a.vector)

def updatedMatrix : Realizes loopCode matrixCode
    (fun a => matrixData ((update a.graph.G a.count (gain a.count) a.state).matrix)) :=
  (((((constant loopCode ratCode 1).sub loopStep).both loopMatrix).then matrixScale).both
    ((loopStep.both (found.then responsePoint)).then matrixScale)).then matrixAdd |>.congr (by
      intro a
      change matrixAddData ((matrixData a.state.matrix).map (fun row => row.map (fun x => (1-stepQ a.graph.m)*x)),
        (matrixData (qresponse (rawMatrix a.vector))).map (fun row => row.map (fun x => stepQ a.graph.m*x))) = _
      rw [matrixScale_data,matrixScale_data]
      exact matrixAdd_data _ _)

def updatedCapacity : Realizes loopEdgeCode ratCode
    (fun x => (update x.1.graph.G x.1.count (gain x.1.count) x.1.state).capacity x.2) :=
  let z := constant loopEdgeCode ratCode 0
  let f := edgeLoop.then found
  ((z.lt (storedU f (fun x => x.2) edgeNumber)).ite
    (z.max ((edgeCoord 1 f (fun x => x.2) edgeNumber).sub (edgeLoop.then loopBase))) z).congr
      (by intro x; simp only [update,decide_eq_true_eq];rfl)
def updateProgram : Realizes loopCode loopCode Loop.updated :=
  (loopGraph.both (loopCount.both
    ((((constant loopCode ratCode 1).add loopStep).mul loopScale).both
      ((loopQuality.sub ((((constant loopCode ratCode 2).mul loopGain).mul
        (loopCount.then natToRat)).mul loopStep)).both
          (updatedMatrix.both (updatedCapacity.tabulateFin loopM)))))).changeOutput
            loopCode Loop.updated (fun _ => rfl)
def next : Realizes loopCode loopCode Loop.next :=
  (((loopScale.pow 4).lt (loopCount.then natToRat)).ite updateProgram (identity loopCode)).congr
    (by intro a; simp only [Loop.next,advance,decide_eq_true_eq];split <;> rfl)

def extract : Realizes extractionInputCode loopCode
    (fun p => ⟨p.1,p.2,extractState p.1.G p.2⟩) :=
  ((((extractionGraph.then numEdges).both extractionCount).then clockProgram).both initializeLoop).then
    next.iterate |>.congr (fun _ => next_iterate _ _)

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.CurrentKS.Realization.poly_wordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

def signs : Realizes frameCode (listCode boolCode)
    (fun a => CurrentKS.RationalInput.signing (RationalSigning.input a.v)) :=
  signerInput.then originalSigningFramed

def simultaneousSigns : Realizes formsCode (listCode boolCode)
    (fun p => CurrentKS.RationalInput.signing (RationalSigning.input
      (fun e => StackedSigning.stack (FormSigning.whiten p.a.2 p.u e)
        (FormSigning.whiten p.b.2 p.v e)))) :=
  whitenPair.then (stack.then signs)

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparsification realization. -/

section

namespace AlgorithmicThinTrees.GraphicHalf.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset
open MetricTests MetricTests.RationalStep Normalization GraphStack
open MetricTests.RationalStep.Stack

def extraction : Realizes problemCode loopCode (fun p => ⟨p.graph,p.r,extractState p.G p.r⟩) :=
  problemView.then extract

def targetBinary : Realizes problemCode binaryNatCode Problem.q :=
  (((extraction.then loopQuality).sub (constant problemCode ratCode 1)).then ratNatFloorBinary)

def targetCount : Realizes problemCode natCode Problem.q := targetBinary.then binaryToNat

def edgeActive : Realizes edgeCode boolCode (fun p => decide (p.2 ∈ p.1.active)) :=
  ((constant edgeCode ratCode 0).lt
    ((number.both (context.then extraction |>.then loopCapacity)).then (getD ratCode 0))).congr
      (by
        intro p
        change decide ((0:ℚ) < (List.ofFn p.1.state.capacity).getD p.2.val 0)=_
        simp only [getD_ofFn,Problem.active,State.active,mem_filter,mem_univ,true_and])

def fullColumn : Realizes edgeCode vectorCode (fun p => List.ofFn (fullColumns p.1.G p.1.active p.2)) :=
  (edgeActive.ite (edgeGraphInput.then incidence)
    (((constant edgeCode ratCode 0).both (context.then problemN)).then (replicateList ratCode))).congr
      (by
        intro p
        simp only [decide_eq_true_eq]
        split_ifs with h
        · rw [fullColumns,ite_eq_left h];rfl
        · rw [fullColumns,ite_eq_right h]
          change List.replicate (p.1.d+1) (0:ℚ)=List.ofFn (fun _ : Fin (p.1.d+1) => (0:ℚ))
          exact (List.ofFn_const _ (0:ℚ)).symm)

def fullRows : Realizes problemCode matrixCode (fun p => matrixData (fullColumns p.G p.active)) :=
  fullColumn.tabulateFin problemM

def reducedEntry : Realizes coordCode ratCode
    (fun x => graphColumns x.1.1.G x.1.1.active x.1.2 x.2) :=
  (((coordIndex.then natSucc).both (coordEdge.then fullColumn)).then (getD ratCode 0)).congr
    (by
      intro x
      change (List.ofFn (fullColumns x.1.1.G x.1.1.active x.1.2)).getD x.2.succ.val 0=_
      rw [getD_ofFn];exact graphColumns_drop _ _ _)

def reducedColumn : Realizes edgeCode vectorCode (fun p => List.ofFn (graphColumns p.1.G p.1.active p.2)) :=
  reducedEntry.tabulateFin (context.then problemD)

def reducedRows : Realizes problemCode matrixCode (fun p => matrixData (graphColumns p.G p.active)) :=
  reducedColumn.tabulateFin problemM

def normalizationParams : Realizes problemCode Normalization.Stack.paramsCode Problem.normalization :=
  (problemD.both (targetCount.both ((constant problemCode ratCode 0).both reducedRows))).changeOutput
    Normalization.Stack.paramsCode Problem.normalization (fun _ => rfl)

def scales : Realizes problemCode vectorCode (fun p => List.ofFn p.scales) :=
  (normalizationParams.both problemCount).then Normalization.Stack.normalized

def positiveMatrix : Realizes problemCode matrixCode (fun p => matrixData (positiveForm p.state.matrix)) :=
  ((extraction.then loopMatrix).both
    ((problemN.both ((constant problemCode ratCode 1).div (problemN.then natToRat))).then
     constantMatrix)).then matrixAdd |>.congr (by
       intro p
       change matrixAddData (matrixData p.state.matrix,matrixData (Matrix.of (fun (_ _ : Fin (p.d+1)) => 1/((p.d+1:ℕ):ℚ))))=_
       change zipDefault (zipDefault (fun p : ℚ×ℚ => p.1+p.2) 0 0) [] []
         (matrixData p.state.matrix,matrixData (Matrix.of (fun (_ _ : Fin (p.d+1)) => 1/((p.d+1:ℕ):ℚ))))=_
       rw [matrixAdd_data]
       simp only [one_div]
       rfl)

def secondMatrix : Realizes problemCode matrixCode (fun p => matrixData (scaledForm p.G p.active p.scales)) :=
  let state := (normalizationParams.both scales).changeOutput Normalization.Stack.stateCode
    (fun p : Problem => ⟨p.normalization,p.scales⟩) (fun _ => rfl)
  state.then Normalization.Stack.gram

def scaledRows : Realizes problemCode matrixCode (fun p => matrixData (scaledColumns p.G p.active p.scales)) :=
  ((scales.both reducedRows).then (vectorScale.zipWith 0 [])).congr (by
    intro p
    change zipDefault (fun p : ℚ×List ℚ => p.2.map (fun x => p.1*x)) 0 []
      (List.ofFn p.scales,List.ofFn (fun e => List.ofFn (graphColumns p.G p.active e)))=_
    rw [zipDefault_ofFn]
    simp only [List.map_ofFn,Function.comp_def]
    rfl)

def forms : Realizes problemCode Signing.Stack.formsCode Problem.forms :=
  (((problemN.both positiveMatrix).both fullRows).both
    ((problemD.both secondMatrix).both scaledRows)).changeOutput Signing.Stack.formsCode
      Problem.forms (fun _ => rfl)

def maskBit : Realizes maskEdgeCode boolCode
    (fun p => if p.2 ∈ p.1.1.active then p.1.2.getD p.2.val false else false) :=
  ((maskEdgeInput.then edgeActive).ite
    ((maskIndex.both (maskContext.then maskSigns)).then (getD boolCode false))
    (constant maskEdgeCode boolCode false)).congr (by intro p;simp only [decide_eq_true_eq])

def mask : Realizes maskCode (listCode boolCode)
    (fun p => List.ofFn (fun e : Fin p.1.m =>
      if e ∈ p.1.active then p.2.getD e.val false else false)) :=
  maskBit.tabulateFin (maskProblem.then problemM)

def signsProgram := forms.then Signing.Stack.simultaneousSigns

def sparsifyProgram : Realizes problemCode (listCode boolCode)
    (fun p => List.ofFn (fun e => decide (e ∈ sparsify p.G p.r))) :=
  (((identity problemCode).both signsProgram).then mask).congr (by
    intro p
    apply congrArg List.ofFn
    funext e
    change (if e ∈ p.active then _ else false)=_
    simp only [sparsify,halfEdges,FormSigning.selected,StackedSigning.selected,
      RationalSigning.selected,mem_inter,mem_filter,mem_univ,true_and]
    by_cases h : e ∈ p.active
    · simp [h,Problem.forms,Problem.active,Problem.state,Problem.scales,Problem.q] at *
    · simp [h] at *)

end AlgorithmicThinTrees.GraphicHalf.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.CurrentKS.Realization.poly_wordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration realization. -/

section

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep MetricTests.RationalStep.Stack OrderedGraph

def halveProgram : Realizes stateCode stateCode halve :=
  (((identity stateCode).both (problem.then sparsifyProgram)).then selectState).congr (by
    intro s
    have he : univ.filter (fun e : Fin s.problem.m =>
        (List.ofFn (fun e => decide (e ∈ sparsify s.problem.G s.problem.r))).getD e.val false)=
        sparsify s.problem.G s.problem.r := by
      ext e
      simp
    change s.restrict _=s.restrict _
    exact congrArg (State.restrict s) he)

def stepProgram (R : ℕ) : Realizes stateCode stateCode (step R) :=
  ((large R).ite halveProgram (identity stateCode)).congr (by intro s;simp [step])

def run (R : ℕ) : Realizes (prodCode natCode stateCode) indicesCode
    (fun p => finishData ((step R)^[p.1] p.2)) := (stepProgram R).iterate.then finish

end AlgorithmicThinTrees.Iteration.Stack

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep OrderedGraph

def treeProgram (R : ℕ) : Realizes problemCode indicesCode (treeData R) :=
  (startProgram.then (run R)).congr (fun p => run_data R (initialCount p.r) (start p).2)

end AlgorithmicThinTrees.Iteration.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputOutput
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input output. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack OrderedGraph Iteration.Stack
open MetricTests.RationalStep.Stack

def eRun (R : ℕ) : Realizes eCode wordCode (eOutput R) :=
  ((ePrepare.then (treeProgram R)).then natToBinary.map).changeOutput wordCode (eOutput R) (by
    intro x
    simp only [treeData,List.map_ofFn,Function.comp_def,id_eq,eOutput,eEdges,
      ExplicitInput.encodeEdges,listCode,FramedMapRoutine.tape,wordCode,binaryNatCode]
    simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat]
    erw [List.map_ofFn]
    rfl)

def bRun (R : ℕ) : Realizes bCode wordCode (bOutput R) :=
  ((bRecords.both (bPrepare.then (treeProgram R))).then pairsOutput).changeOutput
    wordCode (bOutput R) (bOutput_code R)

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input dispatch. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

def largeRun (R : ℕ) : Realizes largeCode wordCode (largeOutput R) :=
  formatTest.dite (binaryTail.then (bRun R)) (explicitTail.then (eRun R))

def program (R : ℕ) : Realizes goodCode wordCode (output R) :=
  singletonTest.dite (constant (fun x : {x : Good // x.val.n=1} => goodCode x.val) wordCode [])
    ((largeRun R).reindex (fun x : {x : Good // x.val.n≠1} => goodCode x.val)
      makeLarge (fun _ => rfl))

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_AlgorithmicMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algorithmic main. -/

section

namespace AlgorithmicThinTrees.InputStack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

def machine (R : ℕ) : CurrentKS.Machine := realizedMachine (program R)

end AlgorithmicThinTrees.InputStack

end

end OAI
end


