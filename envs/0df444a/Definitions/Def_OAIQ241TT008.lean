-- Prove2me | Definitions.Def_OAIQ241TT008
-- name    : OAIQ241TT008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:47.010299+00:00
-- url     : https://prove2.me/theorems/2250c539-5c64-4591-bf00-c3ca89102641
-- title:
--   Definitions bundle OAIQ241TT008 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 319 declarations of OpenAI's Lean: 183 definitions and 136 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.coordinate`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.edgeCoord`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esK`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esT`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.flowCoord`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphDim`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphZeros`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsDim`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsE`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsField`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsK`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsN`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsQ`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsS`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.paramsT`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.pointE`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.pointK`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.pointN`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.pointParser`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.pointQ`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.pointS`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.pointT`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.raw`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.rawEntry`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.rawPoint`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.scalarCount`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.storedU`, `OAI.CurrentKS.PSDCleanRoutine.decode`, `OAI.CurrentKS.PSDCleanRoutine.extract`, `OAI.CurrentKS.PSDCleanRoutine.install`, `OAI.CurrentKS.PSDCleanRoutine.program`, `OAI.CurrentKS.Realization.Realizes.lt`, `OAI.CurrentKS.Realization.Realizes.zipWith`, `OAI.CurrentKS.Realization.binaryToNat`, `OAI.CurrentKS.Realization.matrixEntry`, `OAI.CurrentKS.Realization.numFieldsCode`, `OAI.CurrentKS.Realization.ratFields`, `OAI.CurrentKS.Realization.ratNumBinary`, `OAI.CurrentKS.Realization.select3`, `OAI.CurrentKS.Realization.select7` and 143 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_BinaryAdderCompose`, `MatrixSigning_Arithmetic_BinaryAddressLookup`, `MatrixSigning_Arithmetic_ComplexScalarNodes`, `MatrixSigning_Arithmetic_DivisionInput`, `MatrixSigning_Arithmetic_FixedBinaryAdder`, `MatrixSigning_Arithmetic_FloorRationalMachine`, `MatrixSigning_Arithmetic_MultiplicationMachine`, `MatrixSigning_Arithmetic_NegativeDivision`, `MatrixSigning_Arithmetic_RationalDivisionStages`, `MatrixSigning_Arithmetic_RationalMultiplyNormalize`, `MatrixSigning_Arithmetic_RationalReciprocalSwap`, `MatrixSigning_Arithmetic_RationalSignClassifier`, `MatrixSigning_Arithmetic_SparseScalarNodes`, `MatrixSigning_Arithmetic_ZeroPaddedRow`, `MatrixSigning_Complexity_ComplexScalarCosts`, `MatrixSigning_Complexity_TerminalWitnessCost`, `MatrixSigning_Encoding_FrameActivity`, `MatrixSigning_Encoding_FramedArrayReplacement`, `MatrixSigning_Encoding_ReusableArrayLookup`, `MatrixSigning_Encoding_SignedQuotientSerializer`, `MatrixSigning_Encoding_SumEncodingSize`, `MatrixSigning_Encoding_UnsignedPairSerializer`, `MatrixSigning_Encoding_WireAppend`, `MatrixSigning_Encoding_WireProgramPrimitives`, `MatrixSigning_Encoding_ZeroArrayConstructor`, `MatrixSigning_Machines_CanonicalUnarySpec`, `MatrixSigning_Machines_ControllerTerminalBound`, `MatrixSigning_Machines_DenseFieldCounter`, `MatrixSigning_Machines_FixedCanonicalize`, `MatrixSigning_Machines_FixedCopySpec`, `MatrixSigning_Machines_FixedDotBody`, `MatrixSigning_Machines_FixedDotMachine`, `MatrixSigning_Machines_FixedDotPrimitives`, `MatrixSigning_Machines_SchurCellMachine`, `MatrixSigning_Machines_SchurCounters`, `MatrixSigning_Machines_SchurDimension`, `MatrixSigning_Machines_SchurEntryMachine`, `MatrixSigning_Machines_SchurOperands`, `MatrixSigning_Machines_SchurReadStage`, `MatrixSigning_Machines_SchurRowLoop`, `MatrixSigning_Machines_SchurTableCorrectness`, `MatrixSigning_Machines_SchurTableInvariant`, `MatrixSigning_Machines_SchurTableMachine`, `MatrixSigning_Machines_SignedFloorMachine`, `MatrixSigning_Machines_SignedFloorSize`, `MatrixSigning_Machines_SparseCoefficientStage`, `MatrixSigning_Machines_TerminalInputBounds`, `MatrixSigning_Machines_TerminalReadStage`, `MatrixSigning_Machines_TerminalSparseAssembly`, `MatrixSigning_Machines_TerminalVectorReplace`, `MatrixSigning_Matrices_DenseMatrixSerialization`, `MatrixSigning_Matrices_MatrixAddressArithmetic`, `MatrixSigning_Matrices_MatrixCursorPreparation`, `MatrixSigning_Matrices_MatrixReadProgram`, `MatrixSigning_Matrices_PivotControllerBody`, `MatrixSigning_Matrices_PivotControllerLoop`, `MatrixSigning_Matrices_PivotDecisionCorrectness`, `MatrixSigning_Matrices_PivotDecisionMachine`, `MatrixSigning_Matrices_PivotDecisionPorts`, `MatrixSigning_Matrices_PivotHistoryMachine`, `MatrixSigning_Matrices_PivotReachableBounds`, `MatrixSigning_Matrices_PivotReplayLoop`, `MatrixSigning_Matrices_PivotRowBody`, `MatrixSigning_Matrices_PivotRowClassify`, `MatrixSigning_Matrices_PivotRowCorrectness`, `MatrixSigning_Matrices_PivotRowFinish`, `MatrixSigning_Matrices_PivotRowInitialize`, `MatrixSigning_Matrices_PivotRowLoop`, `MatrixSigning_Matrices_PivotRowRead`, `MatrixSigning_Matrices_PivotScannerBounds`, `MatrixSigning_Matrices_PivotTerminalMachine`, `MatrixSigning_Matrices_PreservedMatrixRetrieval`, `MatrixSigning_Matrices_RowDotBody`, `MatrixSigning_Matrices_RowDotBounds`, `MatrixSigning_Matrices_RowDotControl`, `MatrixSigning_Matrices_RowDotCounter`, `MatrixSigning_Matrices_RowDotMachine`, `MatrixSigning_Matrices_RowDotPrimitives`, `MatrixSigning_Matrices_SavedPivotPacketMachine`, `MatrixSigning_Optimization_PivotDescentBounds`, `MatrixSigning_Optimization_PivotDescentMachine`, `MatrixSigning_Optimization_PivotWitnessMachine`, `MatrixSigning_Optimization_SchurWitnessHead`, `MatrixSigning_Optimization_StoredWitnessLift`, `MatrixSigning_Optimization_TerminalWitnessMachine`, `MatrixSigning_Potential_SchurLoopState`, `MatrixSigning_Realization_MatrixStructureRealization`, `MatrixSigning_Realization_PSDCleanRoutine`, `MatrixSigning_Realization_RatFieldsRealization`, `MatrixSigning_Realization_ScalarRealization`, `MatrixSigning_Realization_VectorRealization`, `ThinTrees_Encoding_GraphRealization`, `ThinTrees_Pencil_Parameters`, `ThinTrees_Pencil_PointPrograms`, `ThinTrees_Pencil_Realization`, `ThinTrees_Pencil_ScalarConstraintRealization`, `ThinTrees_Pencil_SearchRealization`.
--
--   **Imports.** It imports the bundles `OAIQ241TT004`, `OAIQ241TT005` and `OAIQ241TT006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT010` and `OAIQ241TT011`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ241TT004
import Definitions.Def_OAIQ241TT005
import Definitions.Def_OAIQ241TT006

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAdderCompose
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.BinaryAdder
open KS.W29
open KS.W19 (bitsValue digit)

theorem run_normalized (xs ys first second : List Bool)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = (addBits false xs ys).length + 1) :
    normalizedMachine.run
      (Sequential.liftLeft machine NormalizeOutput.machine (cfg (some 0) xs ys []))
      (first ++ second) =
      Sequential.liftRight machine NormalizeOutput.machine
        (FrameDecoder.config none [] (addBits false xs ys) []) := by
  apply NormalizeOutput.compose_result
  · exact haltsAfter false xs ys [] first hfirst
  · have h := run_add false xs ys [] first hfirst
    change machine.run (cfg (some 0) xs ys []) first = _ at h
    rw [h]
    simp only [List.append_nil]
    rfl
  · exact hsecond

end KS.W01.BinaryAdder

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DenseMatrixSerialization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open KS.W07
open scoped BigOperators

theorem denseMatrixTape_length {n : ℕ} (M : DenseRatMatrix n) :
    (denseMatrixTape M).length = ∑ k : Fin (n * n),
      (2 * (KS.W01.encodeRat (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1
        (finProdFinEquiv.symm k).2)).length + 1) := by
  simp [denseMatrixTape, denseMatrixPayloads, List.length_flatMap,
    List.sum_ofFn, KS.W01.length_frame]

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixCursorPreparation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

theorem denseMatrixBinaryCursor_length_le {n : ℕ} (i j : Fin n) :
    (denseMatrixBinaryCursor i j).length ≤ i.val * n + j.val := by
  change KS.W01.natPayloadLength (i.val * n + j.val) ≤ _
  rw [KS.W01.natPayloadLength_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ReusableArrayLookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W04.ReusableArrayLookup
open KS.W01.FixedStack
open KS.W29.FixedSequential
open KS.W03.MachineCombinators

theorem run_copy (source index bits : List Bool) (hlen : 2 * source.length + 2 ≤ bits.length) :
    copyProgram.toMachine.run
      ⟨some copyProgram.initial, arrayStacks source [] [] [] index⟩ bits =
      ⟨none, arrayStacks source source [] [] index⟩ := by
  have hs : RunSpec copyProgram (arrayStacks source [] [] [] index)
      (arrayStacks source source [] [] index) (2*source.length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine copyPorts)
    intro b hb
    have h := KS.W01.FixedCopy.run_copy_restore copyPorts
      (arrayStacks source [] [] [] index) source b rfl rfl rfl hb
    exact h.trans (congrArg (Config.mk (none : Option (Fin 2)))
      (arrayStacks_copy_update source index))
  exact hs.run_of_le bits hlen

theorem run_cleanup (source work payload bits : List Bool) (hlen : work.length + 1 ≤ bits.length) :
    cleanupProgram.toMachine.run
      ⟨some cleanupProgram.initial, arrayStacks source work payload [] []⟩ bits =
      ⟨none, arrayStacks source [] payload [] []⟩ := by
  have hs : RunSpec (BinaryStackMoves.clearProgram (1 : Fin 5))
      (arrayStacks source work payload [] []) (arrayStacks source [] payload [] []) (work.length+1) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (BinaryStackMoves.clearMachine (1 : Fin 5))
    intro b hb
    have h := BinaryStackMoves.run_clear_stacks (1 : Fin 5)
      (arrayStacks source work payload [] []) b hb
    apply h.trans
    refine config_ext rfl ?_
    intro j
    fin_cases j <;> rfl
  erw [cleanupProgram,run_reoutput]
  exact hs.run_of_le bits hlen

theorem run_program (xs : List (List Bool)) (i : Nat) (hi : i < xs.length)
    (tail bits : List Bool)
    (hlen : 5 * (xs.flatMap KS.W01.frame ++ tail).length + i + 4 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, arrayStacks (xs.flatMap KS.W01.frame ++ tail)
        [] [] [] (List.replicate i true)⟩ bits =
      ⟨none, arrayStacks (xs.flatMap KS.W01.frame ++ tail) [] xs[i] [] []⟩ := by
  let source := xs.flatMap KS.W01.frame ++ tail
  let initial := arrayStacks source [] [] [] (List.replicate i true)
  let copied := arrayStacks source source [] [] (List.replicate i true)
  let selected := arrayStacks source ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) xs[i] [] []
  let final := arrayStacks source [] xs[i] [] []
  have hrest : ∀ b : List Bool, (2 * source.length + i + 1) + (source.length + 1) ≤ b.length →
      lookupAndCleanup.toMachine.run ⟨some lookupAndCleanup.initial, copied⟩ b = ⟨none, final⟩ := by
    intro b hb
    apply run_compose_bounded lookupProgram cleanupProgram copied selected final
      (2 * source.length + i + 1) (source.length + 1)
    · exact fun b hb => run_lookup xs i hi tail b hb
    · intro b hb
      apply run_cleanup
      exact (Nat.add_le_add_right (suffix_length_le xs i tail) 1).trans hb
    · exact hb
  change (compose copyProgram lookupAndCleanup).toMachine.run
    ⟨some (compose copyProgram lookupAndCleanup).initial, initial⟩ bits = ⟨none, final⟩
  apply run_compose_bounded copyProgram lookupAndCleanup initial copied final
    (2 * source.length + 2) ((2 * source.length + i + 1) + (source.length + 1))
  · exact fun b hb => run_copy source (List.replicate i true) b hb
  · exact hrest
  · dsimp only [source]
    omega

end KS.W04.ReusableArrayLookup

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PreservedMatrixRetrieval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W08

open KS.W07 KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup

theorem run_preservedMatrix_lookup {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n)
    (tail bits : List Bool)
    (hlen : 5 * (denseMatrixTape M ++ tail).length + i.val * n + j.val + 4 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, arrayStacks (denseMatrixTape M ++ tail)
        [] [] [] (denseMatrixCursor i j)⟩ bits =
      ⟨none, arrayStacks (denseMatrixTape M ++ tail) []
        (KS.W01.encodeRat (AccessCounted.readMatrix M i j).value) [] []⟩ := by
  have hi : i.val * n + j.val < (denseMatrixPayloads M).length := by
    rw [denseMatrixPayloads_length]
    exact matrixEntryIndex_lt i j
  have h := run_program (denseMatrixPayloads M) (i.val * n + j.val) hi tail bits
    (by simpa only [denseMatrixTape, Nat.add_assoc] using hlen)
  simpa only [denseMatrixTape, denseMatrixCursor, denseMatrixPayloads_get,
    AccessCounted.readMatrix_value] using h

end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAddressLookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup

theorem run_matrixCursorProgram {n : ℕ} (M : KS.W07.DenseRatMatrix n) (i j : Fin n)
    (bits : List Bool) (hlen : 8 * n * n + 2 ≤ bits.length) :
    matrixCursorProgram.toMachine.run
      ⟨some matrixCursorProgram.initial,
        arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] []⟩ bits =
      ⟨none, arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j)⟩ := by
  have hstart : (fun r => arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j)
      [] [] [] (matrixCursorPorts r)) = ![denseMatrixBinaryCursor i j, [], []] := by
    funext r
    fin_cases r <;> rfl
  have hi := (matrixEntryIndex_lt i j).le
  have hl := denseMatrixBinaryCursor_length_le i j
  have hb : 4 * KS.W19.bitsValue (denseMatrixBinaryCursor i j) +
      4 * (denseMatrixBinaryCursor i j).length + 2 ≤ bits.length := by
    rw [denseMatrixBinaryCursor_value]
    nlinarith
  apply ofMachine_lift_run_eq KS.W03.BinaryToUnary.machine matrixCursorPorts
    (arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [])
    (arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j)) bits
  · have hp : projectPorts matrixCursorPorts
        (⟨some KS.W03.BinaryToUnary.machine.initial,
          arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] []⟩ :
          Config 5 KS.W03.BinaryToUnary.machine.states) =
        KS.W03.BinaryToUnary.machine.init (denseMatrixBinaryCursor i j) := by
      rw [KS.W03.BinaryToUnary.init_eq]
      change Config.mk (some (0 : Fin 8))
        (fun r=>arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [] (matrixCursorPorts r)) =
        Config.mk (some (0 : Fin 8)) ![denseMatrixBinaryCursor i j,[],[]]
      exact congrArg (Config.mk (some (0 : Fin 8))) hstart
    erw [hp,KS.W03.BinaryToUnary.run_input_linear (denseMatrixBinaryCursor i j) bits hb]
    apply congrArg (Config.mk none)
    change ![[],List.replicate (KS.W19.bitsValue (denseMatrixBinaryCursor i j)) true,[]] =
      (fun r=>arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j) (matrixCursorPorts r))
    rw [denseMatrixBinaryCursor_value]
    funext r
    fin_cases r <;> rfl
  · intro r hr
    have h1 : r≠1 := hr (0 : Fin 3)
    have h4 : r≠4 := hr (1 : Fin 3)
    have h3 : r≠3 := hr (2 : Fin 3)
    fin_cases r <;> simp_all [arrayStacks]

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_UnsignedPairSerializer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.UnsignedPairSerializer
open KS.W28
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem reverse_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (wire : List Bool) :
    RunSpec (reverseProgram ports) (registers ports spare [] [] wire.reverse)
      (registers ports spare [] wire []) (wire.length + 1) := by
  intro bits hbits
  change (lift3 KS.W29.NormalizeOutput.machine ports).run
    ⟨some (2 : Fin 3), registers ports spare [] [] wire.reverse⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some 2, registers ports spare [] [] wire.reverse⟩ : Config k 3) =
        KS.W29.FrameDecoder.config (some 2) [] [] wire.reverse := by
      apply congrArg (KS.W29.Config.mk (some (2 : Fin 3)))
      funext j
      fin_cases j <;> simp
    have hr := congrArg (fun c => KS.W29.NormalizeOutput.machine.run c bits) hp
    refine hr.trans ?_
    erw [KS.W29.NormalizeOutput.run_reversed [] wire bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

end KS.W19.UnsignedPairSerializer

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCanonicalize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.FixedCanonicalize
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def program {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (reverseProgram ports) (trimProgram ports)

theorem reverse_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (input payload : List Bool) :
    RunSpec (reverseProgram ports) (registers ports spare input payload [])
      (registers ports spare input [] payload.reverse) (payload.length + 1) := by
  intro bits hb
  have hne : ports 1 ≠ ports 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (ports.injective h)
  have hl : bits.length = (registers ports spare input payload [] (ports 1)).length + 1 := by
    simpa using hb
  have h := KS.W04.BinaryStackMoves.run_move_stacks (ports 1) (ports 2) hne
    (registers ports spare input payload []) bits hl
  refine h.trans ?_
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    by_cases h1 : j = ports 1
    · subst j
      simp [KS.W04.BinaryStackMoves.twoConfig, registers, ports.injective.eq_iff]
    by_cases h2 : j = ports 2
    · subst j
      simp [KS.W04.BinaryStackMoves.twoConfig, registers, ports.injective.eq_iff]
    simp [KS.W04.BinaryStackMoves.twoConfig, registers, h1, h2]

theorem canonicalize_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (input payload : List Bool) :
    RunSpec (program ports) (registers ports spare input payload [])
      (registers ports spare input (Computability.encodeNat (bitsValue payload)) [])
      (2 * payload.length + 2) := by
  have h := (reverse_spec ports spare input payload).compose (trim_spec ports spare input payload)
  have ht : (payload.length + 1) + (payload.length + 1) = 2 * payload.length + 2 := by omega
  rw [ht] at h
  exact h

end KS.W19.FixedCanonicalize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplyNormalize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product productTicks parseTicks prepareProgram

  negativeBit constructorBits pairBits fields signedFraction)

theorem cleanupTicks_le (na da nb db : List Bool) :
    cleanupTicks na da nb db ≤ 3 * (na.length + da.length + nb.length + db.length) + 7 := by
  have hn := KS.W06.RationalCompare.product_length_le na nb
  have hd := KS.W06.RationalCompare.product_length_le da db
  unfold cleanupTicks
  rw [KS.W03.MultiplicationLoop.advance_length, KS.W03.MultiplicationLoop.advance_length]
  omega

theorem normalizeTicks_le (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    normalizeTicks sa na da sb nb db ≤
      1024 * ((pairBits sa na da sb nb db).length + 1) ^ 3 := by
  let S := payloadSize na da nb db
  let N := (pairBits sa na da sb nb db).length + 1
  have hN : N = 2 * S + 7 := by
    dsimp [N,S,payloadSize]
    rw [KS.W06.RationalCompare.pairBits_length]
  have ha := KS.W06.RationalCompare.magnitude_length_le sa na
  have hb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hp := KS.W06.RationalCompare.productTicks_le (magnitude sa na) (magnitude sb nb)
  have hd := KS.W06.RationalCompare.productTicks_le da db
  have hc := cleanupTicks_le (magnitude sa na) da (magnitude sb nb) db
  have hpn : (magnitude sa na).length + (magnitude sb nb).length + 2 ≤ N := by
    dsimp [S,payloadSize] at hN
    omega
  have hdn : da.length + db.length + 2 ≤ N := by
    dsimp [S,payloadSize] at hN
    omega
  have hp' := hp.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hpn 2))
  have hd' := hd.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hdn 2))
  have hn : S + 3 ≤ N := by omega
  have hn' := Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left hn 3)
  have hNsq : N ^ 2 ≤ N ^ 3 := by
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hNlin : N ≤ N ^ 3 := by
    calc
      N = N ^ 1 := by simp
      _ ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  dsimp [normalizeTicks,parseTicks,payloadSize]
  change _ ≤ 1024 * N ^ 3
  dsimp [S,payloadSize] at hN hn'
  omega

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireProgramPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.WireProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem transfer_spec {k : Nat} (source target scratch : Fin k)
    (hst : source ≠ target) (hs : source ≠ scratch) (ht : target ≠ scratch)
    (before : Fin k → List Bool) (htmp : before scratch = []) :
    RunSpec (transferProgram source target scratch) before (transferAfter source target before)
      (2 * (before source).length + 2) := by
  have h1 := RationalMultiply.move_spec source scratch hs before
  have h2 := RationalMultiply.move_spec scratch target ht.symm
    (RationalMultiply.moveAfter source scratch before)
  have he : RationalMultiply.moveAfter scratch target
      (RationalMultiply.moveAfter source scratch before) = transferAfter source target before := by
    funext j
    by_cases hj : j = source
    · subst j
      simp [RationalMultiply.moveAfter, transferAfter, hs, hst]
    · by_cases hk : j = target
      · subst j
        simp [RationalMultiply.moveAfter, transferAfter, hs.symm, ht, hst.symm, htmp]
      · by_cases hr : j = scratch
        · subst j
          simp [RationalMultiply.moveAfter, transferAfter, hs.symm, ht.symm, htmp]
        · simp [RationalMultiply.moveAfter, transferAfter, hj, hk, hr]
  have h := h1.compose h2
  rw [he] at h
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  simp [RationalMultiply.moveAfter, hs.symm, htmp]
  omega

theorem push_spec {k : Nat} (port : Fin k) (b : Bool) (before : Fin k → List Bool) :
    RunSpec (pushProgram port b) before (Function.update before port (b :: before port)) 1 := by
  intro bits hlen
  rcases bits with _ | ⟨coin,tail⟩
  · simp at hlen
  have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
  subst tail
  change (compile (0 : Fin 1) port port (fun _ _ _ =>
    ⟨none,Vector.ofFn (fun j => if j = port then .push b else .stay)⟩)).step
    (⟨some (0 : Fin 1),before⟩ : Config k 1) coin = _
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  by_cases hj : j = port <;>
    simp [Instruction.action, KS.W29.StackAction.apply, Function.update, hj]

end KS.W15.WireProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ComplexScalarNodes
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.ComplexMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.WireProgram

def pairProgram (a b : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose
    (copyProgram b 0 1 (stored_ne_core b hb 0) (stored_ne_core b hb 1) (by decide))
    (copyProgram a 2 1 (stored_ne_core a ha 2) (stored_ne_core a ha 1) (by decide)))
      (transferProgram 2 0 1)

def mulProgram : Program 28 := KS.W29.FixedSequential.liftPorts RationalMultiply.program mulPorts
def addProgram : Program 28 := KS.W29.FixedSequential.liftPorts KS.W13.RationalAdd.program corePorts

def storeProgram (dest : Fin 28) : Program 28 := transferProgram 10 dest 1

def mulNode (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose (pairProgram a b ha hb) mulProgram) (storeProgram dest)
def addNode (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose (pairProgram a b ha hb) addProgram) (storeProgram dest)

end KS.W15.ComplexMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FrameActivity
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.FrameActivity
open KS.W29 KS.W29.Sequential KS.W29.FrameDecoder

theorem activeFor_append (M : BinaryMachine) (c : Config M.states) (xs ys : List Bool) :
    ActiveFor M c (xs ++ ys) ↔ ActiveFor M c xs ∧ ActiveFor M (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => simp [ActiveFor, BinaryMachine.run]
  | cons b bs ih => simp [ActiveFor, BinaryMachine.run, ih, and_assoc]

theorem active_read (payload tail output scratch bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    ActiveFor FrameDecoder.machine
      (config (some 0) (KS.W01.frame payload ++ tail) output scratch) bits := by
  induction payload generalizing scratch bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons, List.length_nil] at hlen
        omega
      subst bs
      exact ⟨Option.some_ne_none _, trivial⟩
  | cons x xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons b₀ bs =>
      cases bs with
      | nil => simp at hlen
      | cons b₁ rest =>
        have hr : rest.length = 2 * xs.length + 1 := by
          simp only [List.length_cons] at hlen
          omega
        change ActiveFor FrameDecoder.machine
          (config (some 0) (false :: x :: (KS.W01.frame xs ++ tail)) output scratch)
          (b₀ :: b₁ :: rest)
        refine ⟨Option.some_ne_none _, ?_⟩
        rw [tag_false_step]
        refine ⟨Option.some_ne_none _, ?_⟩
        rw [data_step]
        exact ih _ _ hr

theorem active_reverse (input output scratch bits : List Bool)
    (hlen : bits.length = scratch.length + 1) :
    ActiveFor FrameDecoder.machine (config (some 2) input output scratch) bits := by
  induction scratch generalizing output bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst bs
      exact ⟨Option.some_ne_none _, trivial⟩
  | cons x xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs.length = xs.length + 1 := by simpa using hlen
      refine ⟨Option.some_ne_none _, ?_⟩
      rw [reverse_step]
      exact ih _ _ hb

theorem haltsAfter_frame (payload tail bits : List Bool)
    (hlen : bits.length = 3 * payload.length + 2) :
    HaltsAfter FrameDecoder.machine (FrameDecoder.machine.init (KS.W01.frame payload ++ tail)) bits := by
  refine ⟨?_, ?_⟩
  · have hi : FrameDecoder.machine.init (KS.W01.frame payload ++ tail) =
        config (some 0) (KS.W01.frame payload ++ tail) [] [] := by
      simp [BinaryMachine.init, FrameDecoder.machine, FiniteDispatch.compile, config]
    rw [hi]
    have hl : (bits.take (2 * payload.length + 1)).length = 2 * payload.length + 1 := by
      simp only [List.length_take, hlen]
      omega
    have hr : (bits.drop (2 * payload.length + 1)).length = payload.length + 1 := by
      simp only [List.length_drop, hlen]
      omega
    rw [← List.take_append_drop (2 * payload.length + 1) bits]
    apply (activeFor_append FrameDecoder.machine
      (config (some 0) (KS.W01.frame payload ++ tail) [] [])
      (bits.take (2 * payload.length + 1)) (bits.drop (2 * payload.length + 1))).mpr
    refine ⟨active_read payload tail [] [] _ hl, ?_⟩
    rw [run_read payload tail [] [] _ hl]
    apply active_reverse
    simpa using hr
  · rw [run_frame payload tail bits hlen]
    rfl

end KS.W19.FrameActivity

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionInput
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionInput
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

theorem first_init (xs d : List Bool) :
    parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d) =
      pack firstPorts (KS.W29.FrameDecoder.machine.init (KS.W01.frame xs ++ KS.W01.frame d))
        (fun _ => []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem second_start (xs d : List Bool) :
    (⟨some parseSecond.initial, «stacks» (KS.W01.frame d) xs [] []⟩ : Config 10 parseSecond.states) =
      pack secondPorts (KS.W29.FrameDecoder.machine.init (KS.W01.frame d ++ []))
        («stacks» [] xs [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [pack, «stacks», secondPorts, KS.W29.BinaryMachine.init]

end KS.W19.DivisionInput

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_FixedBinaryAdder
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.FixedBinaryAdder
open KS.W29 KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem run_bits (xs ys bits : List Bool) (hlen : bits.length = ticks xs ys) :
    BinaryAdder.normalizedMachine.run
      ⟨some BinaryAdder.normalizedMachine.initial, ![xs, ys, []]⟩ bits =
        ⟨none, ![[], result xs ys, []]⟩ := by
  let cut := max xs.length ys.length + 1
  have hfirst : (bits.take cut).length = max xs.length ys.length + 1 := by
    simp only [List.length_take]
    change min cut bits.length = cut
    apply Nat.min_eq_left
    dsimp [cut]
    unfold ticks at hlen
    omega
  have hsecond : (bits.drop cut).length = (result xs ys).length + 1 := by
    simp only [List.length_drop]
    dsimp [cut]
    unfold ticks at hlen
    omega
  have h := BinaryAdder.run_normalized xs ys (bits.take cut) (bits.drop cut) hfirst hsecond
  rw [List.take_append_drop] at h
  have hi : (⟨some BinaryAdder.normalizedMachine.initial,![xs,ys,[]]⟩ :
      KS.W29.Config BinaryAdder.normalizedMachine.states) =
      Sequential.liftLeft BinaryAdder.machine NormalizeOutput.machine (BinaryAdder.cfg (some 0) xs ys []) := by
    apply congrArg₂ KS.W29.Config.mk
    · rfl
    · funext j; fin_cases j <;> rfl
  rw [hi,h]
  apply congrArg₂ KS.W29.Config.mk
  · rfl
  · funext j; fin_cases j <;> rfl

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 BinaryAdder.normalizedMachine ports)

theorem runSpec {k : ℕ} (ports : Fin 3 ↪ Fin k) (store : Fin k → List Bool)
    (xs ys : List Bool) (hx : store (ports 0) = xs) (hy : store (ports 1) = ys)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports) store (output ports store xs ys) (ticks xs ys) := by
  intro bits hbits
  change (lift3 BinaryAdder.normalizedMachine ports).run
    ⟨some BinaryAdder.normalizedMachine.initial, store⟩ bits = _
  apply lift3_run_eq
  · have hi : project ports
        (⟨some BinaryAdder.normalizedMachine.initial, store⟩ :
          Config k BinaryAdder.normalizedMachine.states) =
        ⟨some BinaryAdder.normalizedMachine.initial, ![xs, ys, []]⟩ := by
      change KS.W29.Config.mk _ (fun j => store (ports j)) = KS.W29.Config.mk _ _
      congr 1
      funext j
      fin_cases j
      · exact hx
      · exact hy
      · exact hscratch
    erw [hi, run_bits xs ys bits hbits]
    congr 1
    funext j
    fin_cases j <;> simp [output, Function.update, ports.injective.eq_iff, hscratch]
  · intro j hj
    simp [output, Function.update, hj 0, hj 1]

theorem runSpec_linear {k : ℕ} (ports : Fin 3 ↪ Fin k) (store : Fin k → List Bool)
    (xs ys : List Bool) (hx : store (ports 0) = xs) (hy : store (ports 1) = ys)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports) store (output ports store xs ys) (2 * (xs.length + ys.length) + 3) := by
  apply (runSpec ports store xs ys hx hy hscratch).mono
  exact BinaryAdder.normalized_transition_bound xs ys

end KS.W01.FixedBinaryAdder

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedFloorSize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SignedFloor

theorem floor_encodeInt_length_le_num (q : Rat) :
    (KS.W01.encodeInt ⌊q⌋).length ≤ (KS.W01.encodeInt q.num).length := by
  let raw := (DivisionLoop.process (Computability.encodeNat q.den)
    (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []).1
  have hraw : raw.length = (Computability.encodeNat (KS.W01.intPayload q.num)).length := by
    simpa only [List.length_nil, List.length_reverse, Nat.zero_add] using
      DivisionLoop.process_quotient_length (Computability.encodeNat q.den)
        (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []
  have hcan : (Computability.encodeNat (bitsValue raw)).length ≤ raw.length := by
    rw [← trimBits_eq_encodeNat]
    exact trimBits_length_le raw
  rw [← floor_wire, List.length_cons, KS.W01.length_encodeNat, KS.W01.length_encodeInt]
  change (2 * (Computability.encodeNat (bitsValue raw)).length + 1) + 1 ≤
    2 * (Computability.encodeNat (KS.W01.intPayload q.num)).length + 2
  omega

theorem floor_encodeInt_length_le_input (q : Rat) :
    (KS.W01.encodeInt ⌊q⌋).length ≤ (KS.W01.encodeRat q).length := by
  have h := floor_encodeInt_length_le_num q
  simp only [KS.W01.encodeRat, List.length_append]
  omega

end KS.W19.SignedFloor

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_SignedQuotientSerializer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SignedQuotientSerializer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

theorem emit_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (sign : Bool) (payload : List Bool) :
    RunSpec (emitProgram ports) (registers ports spare [] payload [sign])
      (registers ports spare [] [] (wire sign payload).reverse) (2 * payload.length + 1) := by
  intro bits hb
  change (lift3 (KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)) ports).run
    ⟨some (2 : Fin 5), registers ports spare [] payload [sign]⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (2 : Fin 5), registers ports spare [] payload [sign]⟩ : Config k 5) =
        KS.W28.PositiveWireSerializer.cfg (some 2) [] payload [sign] := by
      apply congrArg (KS.W29.Config.mk (some (2 : Fin 5)))
      funext j
      fin_cases j <;> simp
    have hr := congrArg (fun c => (KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)).run c bits) hp
    refine hr.trans ?_
    erw [KS.W29.BinaryMachine.withEntry_run,KS.W28.PositiveWireSerializer.run_den payload [sign] bits hb]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp [wire,List.reverse_cons]
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

theorem serialize_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (sign : Bool) (payload : List Bool) :
    RunSpec (program ports) (registers ports spare [] payload [sign])
      (registers ports spare [] (wire sign payload) []) (4 * payload.length + 4) := by
  have h := (emit_spec ports spare sign payload).compose
    (UnsignedPairSerializer.reverse_spec ports spare (wire sign payload))
  have ht : (2 * payload.length + 1) + ((wire sign payload).length + 1) =
      4 * payload.length + 4 := by
    simp only [wire, List.length_cons, KS.W01.length_frame]
    omega
  rw [ht] at h
  exact h

end KS.W19.SignedQuotientSerializer

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedFloorMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SignedFloorMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def canon : Program 11 := FixedCanonicalize.program canonPorts
def finish : Program 11 := compose canon emit

theorem strip_spec (sign : Bool) (tail : List Bool) :
    RunSpec strip («stacks» (sign :: tail) [] [] [] []) («stacks» tail [] [] [] [sign]) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hb
  cases bits with
  | nil => simp at hb
  | cons coin rest =>
    have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simpa using hb
    subst rest
    simp only [Machine.run]
    erw [step_compile]
    cases sign <;> apply KS.W19.FixedRun.config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

theorem canon_spec (sign : Bool) (d q r : List Bool) :
    RunSpec canon («stacks» [] d q r [sign])
      («stacks» [] d (DivisionOutput.canonical q) r [sign]) (2 * q.length + 2) := by
  have h := FixedCanonicalize.canonicalize_spec canonPorts («stacks» [] d q r [sign]) [] q
  have hi : UnsignedPairSerializer.registers canonPorts («stacks» [] d q r [sign]) [] q [] =
      «stacks» [] d q r [sign] := by funext j; fin_cases j <;> rfl
  have ho : UnsignedPairSerializer.registers canonPorts («stacks» [] d q r [sign]) [] (DivisionOutput.canonical q) [] =
      «stacks» [] d (DivisionOutput.canonical q) r [sign] := by funext j; fin_cases j <;> rfl
  dsimp only [DivisionOutput.canonical] at ho
  simp only [hi, ho] at h
  exact h

theorem emit_spec (sign : Bool) (d q r : List Bool) :
    RunSpec emit («stacks» [] d q r [sign])
      («stacks» [] d (SignedQuotientSerializer.wire sign q) r []) (4 * q.length + 4) := by
  have h := SignedQuotientSerializer.serialize_spec outputPorts («stacks» [] d q r [sign]) sign q
  have hi : UnsignedPairSerializer.registers outputPorts («stacks» [] d q r [sign]) [] q [sign] =
      «stacks» [] d q r [sign] := by funext j; fin_cases j <;> rfl
  have ho : UnsignedPairSerializer.registers outputPorts («stacks» [] d q r [sign]) []
      (SignedQuotientSerializer.wire sign q) [] = «stacks» [] d (SignedQuotientSerializer.wire sign q) r [] := by
    funext j
    fin_cases j <;> rfl
  simp only [hi, ho] at h
  exact h

theorem finish_spec (sign : Bool) (d q r : List Bool) :
    RunSpec finish («stacks» [] d q r [sign])
      («stacks» [] d (sign :: KS.W01.encodeNat (bitsValue q)) r []) (6 * q.length + 6) := by
  have h := (canon_spec sign d q r).compose (emit_spec sign d (DivisionOutput.canonical q) r)
  apply h.mono
  have hl := DivisionOutput.canonical_length q
  omega

end KS.W19.SignedFloorMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_FloorRationalMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W20.FloorRationalMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19

theorem ticks_le_polynomial (q : ℚ) :
    ticks q ≤ KS.W29.polynomialFuel 64 2 (KS.W01.encodeRat q).length := by
  have hr := DivisionLoop.process_remainder_length (Computability.encodeNat q.den)
    (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []
  simp only [List.length_nil, List.length_reverse, Nat.zero_max] at hr
  change (SignedFloorMachine.rationalRemainder q).length ≤
    (Computability.encodeNat q.den).length +
      (Computability.encodeNat (KS.W01.intPayload q.num)).length at hr
  have hi := SignedFloor.floor_encodeInt_length_le_input q
  have hparts : (Computability.encodeNat q.den).length +
      (Computability.encodeNat (KS.W01.intPayload q.num)).length ≤ (KS.W01.encodeRat q).length := by
    rw [KS.W01.length_encodeRat]
    change KS.W01.natPayloadLength q.den + KS.W01.natPayloadLength (KS.W01.intPayload q.num) ≤ _
    omega
  unfold ticks KS.W29.polynomialFuel
  nlinarith [Nat.zero_le ((KS.W01.encodeRat q).length ^ 2)]

end KS.W20.FloorRationalMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.MultiplicationMachine

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator

def program : Program 7 :=
  compose (compose KS.W03.MultiplicationInitialize.program KS.W03.MultiplicationLoop.program)
    KS.W03.MultiplicationNormalize.program

def machine : Machine := program.toMachine

@[simp] theorem stack_count : machine.stackCount = 7 := rfl
@[simp] theorem state_count : machine.states = 20 := rfl
@[simp] theorem input_port : machine.inputStack = (0 : Fin 7) := rfl
@[simp] theorem output_port : machine.outputStack = (3 : Fin 7) := rfl

end KS.W03.MultiplicationMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalSwap
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem transfer_spec (source target scratch : Fin 13)
    (hst : source ≠ target) (hsc : source ≠ scratch) (hct : scratch ≠ target)
    (before : Fin 13 → List Bool) (ht : before target = []) (hc : before scratch = []) :
    RunSpec (transfer source target scratch) before (transferred before source target)
      (2 * (before source).length + 2) := by
  let mid : Fin 13 → List Bool := fun j =>
    if j = source then [] else if j = scratch then (before source).reverse else before j
  have hfirst : RunSpec (KS.W04.BinaryStackMoves.moveProgram source scratch)
      before mid ((before source).length + 1) := by
    intro bits hlen
    have h := KS.W04.BinaryStackMoves.run_move_stacks source scratch hsc before bits hlen
    refine (KS.W19.MachineTransport.run_ofMachine
      (KS.W04.BinaryStackMoves.moveMachine source scratch) _ bits).trans ?_
    refine h.trans ?_
    apply config_ext
    · rfl
    · intro j
      simp only [KS.W04.BinaryStackMoves.twoConfig, hc, List.append_nil, mid]
  have hsecond : RunSpec (KS.W04.BinaryStackMoves.moveProgram scratch target)
      mid (transferred before source target) ((before source).length + 1) := by
    intro bits hlen
    have hmid : mid scratch = (before source).reverse := by simp [mid, Ne.symm hsc]
    have h := KS.W04.BinaryStackMoves.run_move_stacks scratch target hct mid bits
      (by simpa only [hmid, List.length_reverse] using hlen)
    refine (KS.W19.MachineTransport.run_ofMachine
      (KS.W04.BinaryStackMoves.moveMachine scratch target) _ bits).trans ?_
    refine h.trans ?_
    apply config_ext
    · rfl
    · intro j
      by_cases hs : j = source
      · subst j
        simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, hst, hsc]
      · by_cases hj : j = target
        · subst j
          simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, Ne.symm hst,
            Ne.symm hsc, Ne.symm hct, ht]
        · by_cases hk : j = scratch
          · subst j
            simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, Ne.symm hsc, hct, hc]
          · simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, hs, hj, hk]
  have h := hfirst.compose hsecond
  convert h using 1 <;> first | rfl | omega

theorem saveNumerator_spec (n d : List Bool) (sgn : Bool) :
    RunSpec saveNumerator (RationalMagnitudeMachine.state n d sgn)
      (savedState n d sgn) (2 * n.length + 2) := by
  have h := transfer_spec 10 9 8 (by decide) (by decide) (by decide)
    (RationalMagnitudeMachine.state n d sgn) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> rfl

theorem shiftDenominator_spec (n d : List Bool) (sgn : Bool) :
    RunSpec shiftDenominator (savedState n d sgn) (shiftedState n d sgn) (2 * d.length + 2) := by
  have h := transfer_spec 11 10 8 (by decide) (by decide) (by decide)
    (savedState n d sgn) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> rfl

theorem restoreNumerator_spec (n d : List Bool) (sgn : Bool) :
    RunSpec restoreNumerator (shiftedState n d sgn)
      (RationalMagnitudeMachine.state d n sgn) (2 * n.length + 2) := by
  have h := transfer_spec 9 11 8 (by decide) (by decide) (by decide)
    (shiftedState n d sgn) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> rfl

theorem swap_spec (n d : List Bool) (sgn : Bool) :
    RunSpec swap (RationalMagnitudeMachine.state n d sgn)
      (RationalMagnitudeMachine.state d n sgn) (4 * n.length + 2 * d.length + 6) := by
  have h := (saveNumerator_spec n d sgn).compose
    ((shiftDenominator_spec n d sgn).compose (restoreNumerator_spec n d sgn))
  convert h using 1 <;> first | rfl | omega

end KS.W30.RationalReciprocal

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalDivisionStages
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem liftCore_spec (P : Program 13) (before after : Fin 13 → List Bool)
    (den num : List Bool) (ticks : ℕ) (h : RunSpec P before after ticks) :
    RunSpec (liftCore P) («stacks» before den num) («stacks» after den num) ticks :=
  KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before after _ _ ticks h
    (stacks_core before den num) (stacks_core after den num) (stacks_spare before after den num)

theorem storeDenominator_spec (q r : ℚ) :
    RunSpec storeDenominator
      («stacks» (KS.W06.SingleRationalParser.canonicalState q (KS.W01.encodeRat r)) [] [])
      («stacks» (RationalReciprocal.canonicalState q) (KS.W01.encodeRat r) [])
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (0 : Fin 15) 13 8 (by decide) (by decide) (by decide)
    («stacks» (KS.W06.SingleRationalParser.canonicalState q (KS.W01.encodeRat r)) [] []) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W15.WireProgram.transferAfter, «stacks», RationalReciprocal.canonicalState, RationalMagnitudeMachine.state, RationalMagnitudeMachine.«stacks», KS.W06.SingleRationalParser.canonicalState, KS.W06.SingleRationalParser.state])

theorem serializeNumerator_spec (q r : ℚ) :
    RunSpec serializeNumerator
      («stacks» (RationalReciprocal.canonicalState q) (KS.W01.encodeRat r) [])
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat q)) (KS.W01.encodeRat r) [])
      (serializerTicks q) :=
  liftCore_spec _ _ _ _ [] _ (KS.W01.SignedRationalSerializer.serializes_rational q)

theorem storeNumerator_spec (q r : ℚ) :
    RunSpec storeNumerator
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat q)) (KS.W01.encodeRat r) [])
      («stacks» (RationalReciprocal.inputState []) (KS.W01.encodeRat r) (KS.W01.encodeRat q))
      (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (10 : Fin 15) 14 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat q)) (KS.W01.encodeRat r) []) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W15.WireProgram.transferAfter, «stacks», RationalReciprocal.inputState, RationalReciprocal.outputState, KS.W06.SingleRationalParser.inputState, KS.W01.SignedRationalSerializer.outputState])

theorem restoreDenominator_spec (q r : ℚ) :
    RunSpec restoreDenominator
      («stacks» (RationalReciprocal.inputState []) (KS.W01.encodeRat r) (KS.W01.encodeRat q))
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r)) [] (KS.W01.encodeRat q))
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (13 : Fin 15) 0 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.inputState []) (KS.W01.encodeRat r) (KS.W01.encodeRat q)) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W15.WireProgram.transferAfter, «stacks», RationalReciprocal.inputState, KS.W06.SingleRationalParser.inputState])

theorem prepareInverse_spec (q r : ℚ) :
    RunSpec prepareInverse
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      (2 * KS.W01.ratLength r⁻¹ + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (10 : Fin 15) 0 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q)) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W15.WireProgram.transferAfter, «stacks», RationalReciprocal.inputState, RationalReciprocal.outputState, KS.W06.SingleRationalParser.inputState, KS.W01.SignedRationalSerializer.outputState])

theorem prependNumerator_spec (q r : ℚ) :
    RunSpec prependNumerator
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      (inputState (inputBits q r⁻¹)) (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (14 : Fin 15) 0 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q)) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W15.WireProgram.transferAfter, «stacks», inputState, inputBits, RationalReciprocal.inputState, KS.W06.SingleRationalParser.inputState])

end KS.W30.RationalDivision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_SumEncodingSize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

def sumBudget (xs : List ℚ) : ℕ := (xs.map ratLength).sum + xs.length

@[simp] theorem sumBudget_nil : sumBudget [] = 0 := rfl

@[simp] theorem sumBudget_cons (q : ℚ) (xs : List ℚ) :
    sumBudget (q :: xs) = ratLength q + sumBudget xs + 1 := by
  simp only [sumBudget, List.map_cons, List.sum_cons, List.length_cons]
  omega

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def multiplyProgram : Program 19 :=
  KS.W29.FixedSequential.liftPorts KS.W15.RationalMultiply.program (initialPorts 13 (by decide))

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotBody
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def additionProgram : Program 19 :=
  KS.W29.FixedSequential.liftPorts KS.W13.RationalAdd.program (initialPorts 16 (by decide))

def body : Program 19 :=
  compose (compose (compose (compose (compose decodeProgram multiplyProgram)
    (transferProgram 10 0)) (transferProgram 17 0)) additionProgram) (transferProgram 10 17)

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 19 := compose «initialize_» (loopProgram body)

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotCounter
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def incrementAdd : Program 29 := KS.W13.RationalAdd.canonicalAddProgram incrementPorts

def incrementProgram : Program 29 := compose (compose oneProgram incrementAdd)
  (StackTransfer.program 7 24 26)

theorem increment_spec (s : Fin 29 → List Bool) (k : ℕ)
    (hk : s 24 = Computability.encodeNat k) (h7 : s 7 = []) (h26 : s 26 = []) :
    RunSpec incrementProgram s (put s 24 (Computability.encodeNat (k + 1)))
      (incrementTicks k) := by
  let t := put s 7 [true]
  let u := put (put s 24 []) 7 (Computability.encodeNat (k + 1))
  have h1 : RunSpec oneProgram s t 1 := by simpa [t, h7] using one_spec s
  have hv : KS.W13.RationalAdd.addResult (Computability.encodeNat k) [true] =
      Computability.encodeNat (k + 1) := by
    simp [KS.W13.RationalAdd.addResult, KS.W19.bitsValue_encodeNat, KS.W19.bitsValue,
      KS.W19.digit]
  have h2 : RunSpec incrementAdd t u
      (KS.W13.RationalAdd.canonicalAddTicks (Computability.encodeNat k) [true]) := by
    convert KS.W13.RationalAdd.canonicalAdd_spec incrementPorts s
      (Computability.encodeNat k) [true] using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> fin_cases j <;> simp [t, u, put, KS.W19.UnsignedPairSerializer.registers, incrementPorts, hk, h26, hv])
  have h3 := StackTransfer.spec (7 : Fin 29) 24 26 (by decide) (by decide) (by decide) u
    (by simp [u, put, h26])
  have he : StackTransfer.after 7 24 u = put s 24 (Computability.encodeNat (k + 1)) := by
    funext j
    fin_cases j <;> simp [StackTransfer.after, put, u, h7]
  have h := (h1.compose h2).compose h3
  simpa [incrementProgram, incrementTicks, he, u, put] using h

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixAddressArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W08.MatrixAddress

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator

def addProgram : Program 7 := KS.W01.FixedBinaryAdder.program addPorts

def program : Program 7 := compose
  (compose (compose KS.W03.MultiplicationLoop.program addProgram)
    KS.W03.MultiplicationNormalize.program) cleanupProgram

theorem add_spec (col operand product : List Bool) :
    RunSpec addProgram (registers col [] operand product [] [] [])
      (registers [] [] operand (KS.W01.FixedBinaryAdder.result col product) [] [] [])
      (2 * (col.length + product.length) + 3) := by
  have h := KS.W01.FixedBinaryAdder.runSpec_linear addPorts
    (registers col [] operand product [] [] []) col product rfl rfl rfl
  have he : KS.W01.FixedBinaryAdder.output addPorts
      (registers col [] operand product [] [] []) col product =
      registers [] [] operand (KS.W01.FixedBinaryAdder.result col product) [] [] [] := by
    funext j
    fin_cases j <;> simp [KS.W01.FixedBinaryAdder.output, addPorts, registers, Function.update]
  rw [he] at h
  exact h

theorem full_spec (row dim col : List Bool) :
    RunSpec program (registers col row dim [] [] [] [])
      (registers [] [] [] (Computability.encodeNat
        (KS.W19.bitsValue row * KS.W19.bitsValue dim + KS.W19.bitsValue col)) [] [] [])
      (ticks row dim col) := by
  have hm := KS.W03.MultiplicationLoop.loop_spec col row dim []
  have ha := add_spec col (KS.W03.MultiplicationLoop.advance row dim) (rawProduct row dim)
  have hn := KS.W03.MultiplicationNormalize.normalize_spec [] []
    (KS.W03.MultiplicationLoop.advance row dim) (rawAddress row dim col)
  have hc := cleanup_spec (KS.W03.MultiplicationLoop.advance row dim)
    (Computability.encodeNat (KS.W19.bitsValue (rawAddress row dim col)))
  have h := ((hm.compose ha).compose hn).compose hc
  have hv : KS.W19.bitsValue (rawAddress row dim col) =
      KS.W19.bitsValue row * KS.W19.bitsValue dim + KS.W19.bitsValue col := by
    rw [rawAddress, KS.W01.FixedBinaryAdder.result_value, rawProduct, loop_zero_correct]
    omega
  rw [hv] at h
  exact h

theorem run_encoded (row dim col : ℕ) (bits : List Bool)
    (hlen : 32 * (Nat.size row + Nat.size dim + Nat.size col + 1) ^ 2 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, registers (Computability.encodeNat col)
        (Computability.encodeNat row) (Computability.encodeNat dim) [] [] [] []⟩ bits =
      ⟨none, registers [] [] [] (Computability.encodeNat (row * dim + col)) [] [] []⟩ := by
  have h := full_spec (Computability.encodeNat row) (Computability.encodeNat dim)
    (Computability.encodeNat col)
  have hb := ticks_le (Computability.encodeNat row) (Computability.encodeNat dim)
    (Computability.encodeNat col)
  have hr : (Computability.encodeNat row).length = Nat.size row := KS.W01.natPayloadLength_eq_size row
  have hd : (Computability.encodeNat dim).length = Nat.size dim := KS.W01.natPayloadLength_eq_size dim
  have hc : (Computability.encodeNat col).length = Nat.size col := KS.W01.natPayloadLength_eq_size col
  rw [hr, hd, hc] at hb
  simpa only [KS.W19.bitsValue_encodeNat] using h.run_of_le bits (hb.trans hlen)

theorem run_matrix_address {n : ℕ} (i j : Fin n) (bits : List Bool)
    (hlen : 512 * (n + 1) ^ 2 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, registers (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) [] [] [] []⟩ bits =
      ⟨none, registers [] [] [] (KS.W08.denseMatrixBinaryCursor i j) [] [] []⟩ := by
  simpa only [KS.W08.denseMatrixBinaryCursor] using
    run_encoded i.val n j.val bits ((matrix_address_budget i j).trans hlen)

end KS.W08.MatrixAddress

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixReadProgram
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.MatrixRead

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W03.MultiplicationBody KS.W03.MachineCombinators

def addressProgram : Program 8 := KS.W29.FixedSequential.liftPorts MatrixAddress.program addressPorts

def program : Program 8 := compose addressProgram accessProgram

theorem run_address {n : ℕ} (source : List Bool) (i j : Fin n) (bits : List Bool)
    (hlen : 512 * (n + 1) ^ 2 ≤ bits.length) :
    addressProgram.toMachine.run
      ⟨some addressProgram.initial, workspace source (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) []⟩ bits =
      ⟨none, workspace source [] [] [] (denseMatrixBinaryCursor i j)⟩ := by
  have hs : RunSpec MatrixAddress.program
      (registers (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n) [] [] [] [])
      (registers [] [] [] (denseMatrixBinaryCursor i j) [] [] []) (512*(n+1)^2) := by
    intro coins hcoins
    exact MatrixAddress.run_matrix_address i j coins hcoins.ge
  have hl : RunSpec addressProgram
      (workspace source (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n) [])
      (workspace source [] [] [] (denseMatrixBinaryCursor i j)) (512*(n+1)^2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ addressPorts _ _ _ _ _ hs
    · intro r; fin_cases r <;> rfl
    · intro r; fin_cases r <;> rfl
    · intro r hr
      have h0 : r≠0 := hr (0 : Fin 7)
      have h1 : r≠1 := hr (1 : Fin 7)
      have h2 : r≠2 := hr (2 : Fin 7)
      have h3 : r≠3 := hr (3 : Fin 7)
      fin_cases r <;> simp_all [workspace]
  exact hl.run_of_le bits hlen

end KS.W08.MatrixRead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def readProgram : Program 29 := KS.W29.FixedSequential.liftPorts KS.W08.MatrixRead.program readPorts

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotBody
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def collectProgram : Program 29 :=
  compose (compose (compose (compose decodeProgram copyColumn) copyRow) copyDimension) readProgram

def body : Program 29 := compose (compose collectProgram pairProgram) incrementProgram

theorem pair_spec (s : Fin 29 → List Bool) (a q : ℚ)
    (h0 : s 0 = KS.W01.encodeRat a) (h27 : s 27 = KS.W01.encodeRat q)
    (h4 : s 4 = []) (h26 : s 26 = []) (h28 : s 28 = []) :
    RunSpec pairProgram s
      (put (put (put s 0 []) 27 []) 25
        ((FixedDot.pairWire (a, q)).reverse ++ s 25)) (pairTicks a q) := by
  let s1 := StackTransfer.after 27 28 s
  let s2 := StackTransfer.after 0 28 s1
  let s3 := put s2 28 (KS.W01.frame (s2 28))
  have h1 := StackTransfer.spec (27 : Fin 29) 28 26 (by decide) (by decide) (by decide) s h26
  have h2 := StackTransfer.spec (0 : Fin 29) 28 26 (by decide) (by decide) (by decide) s1
    (by simp [s1, StackTransfer.after, h26])
  have h3 := frame_spec s2 (by simp [s2, s1, StackTransfer.after, h4])
    (by simp [s2, s1, StackTransfer.after, h26])
  have h4' := append_spec s3
  have h := ((h1.compose h2).compose h3).compose h4'
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j
    fin_cases j <;> simp [s1, s2, s3, put, StackTransfer.after, h0, h27, h28,
      FixedDot.pairWire, FixedDot.pairPayload]
  · simp [pairTicks, s1, s2, s3, StackTransfer.after, put, h0, h27, h28]

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotControl
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def loopProgram : Program 29 := KS.W29.FixedLoop.loop body guard

theorem step_empty {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ)
    (i : Fin n) (k : ℕ) (out : List Bool) (coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, boundary M x i [] k out⟩ coin =
      ⟨none, boundary M x i [] k out⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary M x i [] k out⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_cons {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ)
    (i : Fin n) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) (k : ℕ)
    (out : List Bool) (coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, boundary M x i (p :: xs) k out⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial, boundary M x i (p :: xs) k out⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary M x i (p :: xs) k out⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  have hhead : KS.W29.topCode ((boundary M x i (p :: xs) k out) 23) ≠ 0 := by
    change KS.W29.topCode (KS.W01.frame (KS.W01.encodeRat p.2) ++ tailTape xs) ≠ 0
    cases hp : KS.W01.encodeRat p.2 with
    | nil => simp [KS.W01.frame, KS.W29.topCode]
    | cons b bs => simp [KS.W01.frame, KS.W29.topCode]
  simp only [guard, observedHeads, hhead, ↓reduceIte]
  change Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _ =
    Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _
  congr 1
  funext j
  simp [KS.W29.FixedLoop.guardInstruction, Instruction.action, KS.W29.StackAction.apply]

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def prepareProgram : Program 29 := compose copyVector loopProgram

def dotProgram : Program 29 := KS.W29.FixedSequential.liftPorts FixedDot.program dotPorts

def finishProgram : Program 29 := compose (compose clearCounter restoreWire) dotProgram

def program : Program 29 := compose prepareProgram finishProgram

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot
open Matrix
open KS.W01 KS.W01.FixedStack KS.W07
open scoped BigOperators

theorem matrix_entry_length {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    ratLength (DenseRatMatrix.decode M i j) ≤ (KS.W08.denseMatrixTape M).length := by
  apply payload_le_framed
  have h := List.getElem_mem (l := KS.W08.denseMatrixPayloads M)
    (n := i.val * n + j.val) (by simpa using KS.W08.matrixEntryIndex_lt i j)
  simpa only [KS.W08.denseMatrixPayloads_get] using h

theorem vector_entry_length {n : ℕ} (x : Fin n → ℚ) (j : Fin n) :
    ratLength (x j) ≤ (vectorTape x).length := by
  apply payload_le_framed
  simp only [List.mem_ofFn]
  exact ⟨j, rfl⟩

theorem encodeNat_length_le_self (k : ℕ) : (Computability.encodeNat k).length ≤ k := by
  rw [KS.W19.encodeNat_length_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem pair_stream_length {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    (FixedDot.inputWire (rowPairs M i (indexedVector x))).length ≤
      5 * (storedLength M x i + 1) ^ 2 := by
  have hn : n ≤ storedLength M x i := by
    have h := dimension_le_vector x
    unfold storedLength
    omega
  have hsum : (FixedDot.inputWire (rowPairs M i (indexedVector x))).length ≤
      n * (4 * storedLength M x i + 1) := by
    simp only [rowPairs, indexedVector, List.map_ofFn, FixedDot.inputWire,
      List.length_flatMap, List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _j : Fin n, (4 * storedLength M x i + 1) := by
        apply Finset.sum_le_sum
        intro j _
        have ha := matrix_entry_length M i j
        have hq := vector_entry_length x j
        simp only [Function.comp_def, FixedDot.pairWire_length, FixedDot.pairPayload,
          List.length_append]
        unfold ratLength at ha hq
        unfold storedLength
        omega
      _ = _ := by simp
  calc
    _ ≤ n * (4 * storedLength M x i + 1) := hsum
    _ ≤ storedLength M x i * (4 * storedLength M x i + 1) := Nat.mul_le_mul_right _ hn
    _ ≤ _ := by nlinarith

theorem bodyTicks_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i j : Fin n) :
    bodyTicks M (storedLength M x i) i (j, x j) ≤ 2000 * (storedLength M x i + 1) ^ 3 := by
  let L := storedLength M x i
  have hn : n ≤ L := by have h := dimension_le_vector x; dsimp [L, storedLength]; omega
  have hi : i.val ≤ L := i.isLt.le.trans hn
  have hj : j.val ≤ L := j.isLt.le.trans hn
  have hni := encodeNat_length_le_self i.val
  have hnj := encodeNat_length_le_self j.val
  have hnn := encodeNat_length_le_self n
  have hnjs := encodeNat_length_le_self (j.val + 1)
  have ha := matrix_entry_length M i j
  have hq := vector_entry_length x j
  have hla : (encodeRat (DenseRatMatrix.decode M i j)).length ≤ L := by
    dsimp [L, storedLength]; unfold ratLength at ha; omega
  have hlq : (encodeRat (x j)).length ≤ L := by
    dsimp [L, storedLength]; unfold ratLength at hq; omega
  have had := KS.W13.RationalAdd.canonicalAddTicks_le (Computability.encodeNat j.val) [true]
  have hread : 1024 * (n + 1) ^ 2 * (L + 1) ≤ 1024 * (L + 1) ^ 3 := by
    calc
      _ ≤ 1024 * (L + 1) ^ 2 * (L + 1) := by gcongr
      _ = _ := by ring
  unfold bodyTicks collectTicks pairTicks incrementTicks
  simp only [List.length_append, KS.W01.length_frame, List.length_cons, List.length_nil] at *
  change _ ≤ 2000 * (L + 1) ^ 3
  have hl : 60 * L + 60 ≤ 976 * (L + 1) ^ 3 := by nlinarith [Nat.zero_le (L ^ 3)]
  dsimp only [L] at *
  omega

theorem loopTicks_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    loopTicks M (storedLength M x i) i (indexedVector x) ≤
      3000 * (storedLength M x i + 1) ^ 4 := by
  let L := storedLength M x i
  have haux : ∀ xs : List (Fin n × ℚ), (∀ p ∈ xs, p.2 = x p.1) →
      loopTicks M L i xs ≤ 1 + xs.length * (1 + 2000 * (L + 1) ^ 3) := by
    intro xs hx
    induction xs with
    | nil => simp [loopTicks]
    | cons p ps ih =>
        have hp := hx p (by simp)
        have ht := ih (by intro q hq; exact hx q (by simp [hq]))
        have hb := bodyTicks_stored M x i p.1
        rw [← hp] at hb
        simp only [loopTicks, List.length_cons]
        dsimp only [L] at *
        nlinarith
  have h := haux (indexedVector x) (by intro p hp; simp [indexedVector] at hp; rcases hp with ⟨j, rfl⟩; rfl)
  have hn : n ≤ L := by have h := dimension_le_vector x; dsimp [L, storedLength]; omega
  simp only [indexedVector, List.length_ofFn] at h
  calc
    _ ≤ 1 + n * (1 + 2000 * (L + 1) ^ 3) := h
    _ ≤ 1 + L * (1 + 2000 * (L + 1) ^ 3) := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (L ^ 2), Nat.zero_le (L ^ 3)]

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ZeroPaddedRow
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

def zeroFrame : List Bool := KS.W01.frame (KS.W01.encodeRat 0)

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_NegativeDivision
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def divisionProgram : Program 29 := KS.W29.FixedSequential.liftPorts KS.W30.RationalDivision.program divisionPorts

def productProgram : Program 29 := KS.W29.FixedSequential.liftPorts KS.W15.RationalMultiply.program productPorts

def negativeDivisionProgram : Program 29 := compose (compose (compose divisionProgram minusOneProgram)
  (StackTransfer.program 10 0 26)) productProgram

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignClassifier
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalSignClassifier

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare
open KS.W04.CleanRationalCompare

def classifyProgram : Program 13 :=
  ofMachine (compile (0 : Fin 1) 0 9 classifyDispatch)

theorem classify_spec (before : Fin 13 → List Bool) (sign : Bool) (num : List Bool)
    (hs : before 12 = [sign]) (hn : before 10 = num) (ho : before 9 = []) :
    RunSpec classifyProgram before (classifiedState before sign num) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    (compile (0 : Fin 1) (0 : Fin 13) (9 : Fin 13) classifyDispatch)
  intro bits hlen
  obtain ⟨coin, rfl⟩ := List.length_eq_one_iff.mp hlen
  change (compile (0 : Fin 1) (0 : Fin 13) (9 : Fin 13) classifyDispatch).step
    ⟨some (0 : Fin 1), before⟩ coin = _
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  by_cases hj : j = 9
  · subst j
    cases sign <;> cases num <;>
      simp [classifyDispatch, Instruction.action, classifiedState, rawCode,
        observedHeads, KS.W29.topCode, KS.W29.StackAction.apply, hs, hn, ho]
    all_goals
      rename_i head tail
      cases head <;> rfl
  · simp [classifyDispatch, Instruction.action, classifiedState, hj,
      KS.W29.StackAction.apply]

def readProgram : Program 13 := compose SingleRationalParser.program classifyProgram

def readTicks (q : ℚ) : ℕ := 8 * (KS.W01.ratLength q + 1) + 1

def program : Program 13 := compose readProgram cleanupProgram

@[simp] theorem program_output : program.output = 9 := rfl

end KS.W06.RationalSignClassifier

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_ComplexScalarCosts
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.ComplexMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.WireProgram KS.W01

def negNode (a dest : Fin 28) (ha : 16 ≤ a.val) : Program 28 :=
  compose (compose (compose
    (copyProgram a 0 1 (stored_ne_core a ha 0) (stored_ne_core a ha 1) (by decide))
    (literalProgram 0 negativeOneWire)) mulProgram) (storeProgram dest)

end KS.W15.ComplexMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SparseScalarNodes
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SparseScalarNodes
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

def divProgram : Program 28 := liftPorts KS.W30.RationalDivision.program divPorts

def divNode (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose (pairProgram a b ha hb) divProgram) (storeProgram dest)
def divNodeTicks (q r : ℚ) : ℕ := pairTicks (KS.W01.encodeRat q) (KS.W01.encodeRat r) +
  divTicks q r + (2*(KS.W01.encodeRat (q/r)).length+2)

def after (s : Registers) (a b : ℚ) : Registers :=
  put (put (put (put (put (put s 20 1) 21 2) 18 (a+1)) 19 (2*b)) 24 (-(a+1))) 25 (coefficient a b)

def program : Program 28 := compose (KS.W15.WireProgram.literalProgram 20 (KS.W01.encodeRat 1))
  (compose (KS.W15.WireProgram.literalProgram 21 (KS.W01.encodeRat 2))
    (compose (addNode 16 20 18 (by decide) (by decide))
      (compose (mulNode 21 17 19 (by decide) (by decide))
        (compose (negNode 18 24 (by decide)) (divNode 24 19 25 (by decide) (by decide))))))

end KS.W19.SparseScalarNodes

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SparseCoefficientStage
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SparseCoefficientStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

def arithmetic : Program 35 := liftPorts SparseScalarNodes.program ports

def cleanup : Program 35 := KS.W04.CleanRationalCompare.clearListProgram 28 cleanupPorts
def program : Program 35 := compose arithmetic cleanup

end KS.W19.SparseCoefficientStage

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireAppend
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.WireAppend

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem spec {k : ℕ} (source target scratch : Fin k)
    (hst : source ≠ target) (hsc : source ≠ scratch) (hct : scratch ≠ target)
    (before : Fin k → List Bool) (hempty : before scratch = []) :
    RunSpec (program source target scratch) before (after source target before)
      (2 * (before source).length + 2) := by
  have h₁ := move_spec source scratch hsc before
  have h₂ := move_spec scratch target hct (moveAfter source scratch before)
  have h := h₁.compose h₂
  have he : moveAfter scratch target (moveAfter source scratch before) =
      after source target before := by
    funext j
    by_cases hjs : j = source
    · subst j
      simp [moveAfter, after, hst, hsc]
    · by_cases hjt : j = target
      · subst j
        simp [moveAfter, after, Ne.symm hst, Ne.symm hsc, Ne.symm hct, hempty]
      · by_cases hjc : j = scratch
        · subst j
          simp [moveAfter, after, hjs, hjt, hempty]
        · simp [moveAfter, after, hjs, hjt, hjc]
  have hf : (before source).length + 1 +
      ((moveAfter source scratch before) scratch).length + 1 =
      2 * (before source).length + 2 := by
    simp [moveAfter, Ne.symm hsc, hempty]
    omega
  simpa only [program, he, ← Nat.add_assoc, hf] using h

end KS.W07.WireAppend

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCopySpec
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07
open KS.W29.FixedSequential KS.W03.MachineCombinators

theorem fixedCopy_spec {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (before : Fin k → List Bool) (xs : List Bool)
    (hsrc : before (ports 0) = xs) (hdst : before (ports 1) = [])
    (hscratch : before (ports 2) = []) :
    RunSpec (KS.W01.FixedCopy.program ports) before
      (Function.update before (ports 1) xs) (2 * xs.length + 2) := by
  unfold KS.W01.FixedCopy.program
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hlen
  exact KS.W01.FixedCopy.run_copy_restore ports before xs bits hsrc hdst hscratch hlen

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurReadStage
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurReadStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def reader : Program 32 := liftPorts KS.W08.MatrixRead.program readPorts

theorem copy_spec (source target : Fin 32) (hs : source ≠ target)
    (hc : source ≠ 16) (ht : target ≠ 16) (before : Fin 32 → List Bool)
    (he : before target = []) (h16 : before 16 = []) :
    RunSpec (copyProgram source target hs hc ht) before
      (Function.update before target (before source)) (2*(before source).length+2) := by
  exact KS.W07.fixedCopy_spec (copyPorts source target hs hc ht)
    before (before source) rfl he h16

theorem prepare_spec (before : Fin 32 → List Bool) (hw : WorkClear before) (row col : Bool) :
    RunSpec (prepare row col) before
      (readPrepared before (before (colSource col)) (before (rowSource row)) (before 26))
      (prepareTicks before row col) := by
  have h₁ := copy_spec 26 2 (by decide) (by decide) (by decide) before
    (hw _ (by decide)) (hw _ (by decide))
  have h₂ := copy_spec (rowSource row) 1 (by cases row <;> decide)
    (by cases row <;> decide) (by decide) (Function.update before 2 (before 26))
    (by simpa using hw 1 (by decide)) (by simpa using hw 16 (by decide))
  have h₃ := copy_spec (colSource col) 0 (by cases col <;> decide)
    (by cases col <;> decide) (by decide)
    (Function.update (Function.update before 2 (before 26)) 1 (before (rowSource row)))
    (by simpa using hw 0 (by decide)) (by simpa using hw 16 (by decide))
  have hrow : (Function.update before 2 (before 26)) (rowSource row) = before (rowSource row) := by
    cases row <;> rfl
  rw [hrow] at h₂
  have hcol : (Function.update (Function.update before 2 (before 26)) 1
      (before (rowSource row))) (colSource col) = before (colSource col) := by
    cases col <;> rfl
  rw [hcol] at h₃
  exact h₁.compose (h₂.compose h₃)

def program (row col : Bool) (k : Fin 4) : Program 32 :=
  compose (prepare row col) (compose reader (WireAppend.program 0 (destination k) 16))

end KS.W07.SchurReadStage

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalReadStage
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalReadStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07

def program (diagonal : Bool) : Program 35 :=
  liftPorts (SchurReadStage.program diagonal true (slot diagonal)) ports

def readTicks {n : ℕ} (M : DenseRatMatrix n) (B : ℕ) (i j : Fin n)
    (s : Fin 35 → List Bool) (diagonal : Bool) : ℕ :=
  SchurReadStage.prepareTicks (fun k => s (ports k)) diagonal true +
    (1024*(n+1)^2*(B+1)+(2*KS.W01.ratLength (DenseRatMatrix.decode M i j)+2))

end KS.W19.TerminalReadStage

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayReplacement
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack KS.W03.MachineCombinators
open KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup (run_compose_bounded)

def replaceFuel («prefix» : List (List Bool)) (old new : List Bool) : ℕ :=
  KS.W11.FramedArray.scanFuel «prefix» + 2 * old.length +
    2 * (KS.W01.frame new).length + («prefix».flatMap KS.W01.frame).length + 4

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ZeroArrayConstructor
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.ZeroArrayConstructor
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem zeroFrame_length : zeroFrame.length = 11 := by decide
def zeroTape (n : ℕ) : List Bool := (List.replicate n zeroFrame).flatten

theorem zeroTape_succ (n : ℕ) : zeroTape (n + 1) = zeroFrame ++ zeroTape n := by
  simp [zeroTape, List.replicate_succ]

theorem zeroTape_length (n : ℕ) : (zeroTape n).length = n * zeroFrame.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [zeroTape_succ, List.length_append, ih]
      simp [Nat.succ_mul, Nat.add_comm]

end KS.W11.ZeroArrayConstructor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalVectorReplace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalVectorReplace
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators Matrix

def unitPayloads (n : ℕ) : List (List Bool) := (zeroPayloads n).set 0 (KS.W01.encodeRat 1)

theorem zeroTape_eq (n : ℕ) : KS.W11.ZeroArrayConstructor.zeroTape n =
    (zeroPayloads n).flatMap KS.W01.frame := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [KS.W11.ZeroArrayConstructor.zeroTape_succ, ih]
    simp only [zeroPayloads, List.replicate_succ, List.flatMap_cons,
      KS.W11.ZeroArrayConstructor.zeroFrame]

end KS.W19.TerminalVectorReplace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalSparseAssembly
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalSparseAssembly
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.TerminalVectorReplace

def headTicks (n : ℕ) (c : ℚ) : ℕ := TerminalZeroVector.ticks n +
  (4*(KS.W01.encodeRat c).length+3 +
    (2*(KS.W01.frame (KS.W01.encodeRat c)).length+2 +
      (2*((zeroPayloads n).flatMap KS.W01.frame).length+2*(KS.W01.frame (KS.W01.encodeRat c)).length+3)))

def ticks (n j : ℕ) (c : ℚ) : ℕ := headTicks n c +
  (oneFrame.length+1 + ((4*j+4*(Computability.encodeNat j).length+2) +
    (2*(((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame).length+
      2*oneFrame.length+j+3)))

end KS.W19.TerminalSparseAssembly

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_TerminalWitnessMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07 Matrix

def inputState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    Fin 35 → List Bool := fun i => if i=31 then KS.W08.denseMatrixTape M else
      if i=26 then Computability.encodeNat (n+1) else if i=32 then saved else
      if i=30 then Computability.encodeNat j.val else []

def collected {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    Fin 35 → List Bool :=
  Function.update (Function.update (Function.update (inputState saved M j) 33
    (Computability.encodeNat j.val)) 19 (KS.W01.encodeRat (DenseRatMatrix.decode M j j)))
    20 (KS.W01.encodeRat (DenseRatMatrix.decode M 0 j))

def copyIndex : Program 35 := KS.W15.WireProgram.copyProgram 30 33 16
  (by decide) (by decide) (by decide)
def collect : Program 35 := compose copyIndex
  (compose (TerminalReadStage.program true) (TerminalReadStage.program false))

def collectTicks {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ) (j : Fin (n+1)) : ℕ :=
  let s := Function.update (inputState saved M j) 33 (Computability.encodeNat j.val)
  (2*(Computability.encodeNat j.val).length+2) +
    (TerminalReadStage.readTicks M B j j s true +
      TerminalReadStage.readTicks M B 0 j
        (Function.update s 19 (KS.W01.encodeRat (DenseRatMatrix.decode M j j))) false)

def coefficient {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) : ℚ :=
  SparseScalarNodes.coefficient (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)

def program : Program 35 := compose collect
  (compose SparseCoefficientStage.program TerminalSparseAssembly.program)

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_TerminalWitnessCost
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01 KS.W07

theorem raw_length_le (n : ℕ) : (Computability.encodeNat n).length ≤ n := by
  rw [encodeNat_length_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem zero_payload_length (n : ℕ) :
    ((TerminalVectorReplace.zeroPayloads n).flatMap KS.W01.frame).length = 11*n := by
  rw [← TerminalVectorReplace.zeroTape_eq,KS.W11.ZeroArrayConstructor.zeroTape_length,
    KS.W11.ZeroArrayConstructor.zeroFrame_length]
  omega

theorem head_payload_length (n : ℕ) (c : ℚ) :
    (((TerminalVectorReplace.zeroPayloads (n+1)).set 0 (encodeRat c)).flatMap KS.W01.frame).length =
      2*ratLength c+1+11*n := by
  have he : ((TerminalVectorReplace.zeroPayloads (n+1)).set 0 (encodeRat c)).flatMap KS.W01.frame =
      KS.W01.frame (encodeRat c) ++ (TerminalVectorReplace.zeroPayloads n).flatMap KS.W01.frame := by
    simp [TerminalVectorReplace.zeroPayloads,List.replicate_succ]
  rw [he,List.length_append,KS.W01.length_frame,zero_payload_length]
  rfl

theorem assemblyTicks_linear (n : ℕ) (j : Fin (n+1)) (c : ℚ) :
    TerminalSparseAssembly.ticks (n+1) j.val c ≤ 100*((n+1)+ratLength c+1) := by
  have hn := raw_length_le (n+1)
  have hj := raw_length_le j.val
  have hji := j.isLt
  have hone : TerminalVectorReplace.oneFrame.length = 15 := by decide
  unfold TerminalSparseAssembly.ticks TerminalSparseAssembly.headTicks TerminalZeroVector.ticks
  simp only [zero_payload_length,head_payload_length,hone,KS.W01.length_frame]
  dsimp only [ratLength]
  omega

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_CanonicalUnarySpec
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07
open KS.W29.FixedSequential KS.W03.MachineCombinators

theorem canonicalUnary_spec (n : ℕ) :
    RunSpec KS.W03.BinaryToUnary.program ![Computability.encodeNat n, [], []]
      ![[], List.replicate n true, []]
      (4*n + 4*(Computability.encodeNat n).length + 2) := by
  unfold KS.W03.BinaryToUnary.program
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine KS.W03.BinaryToUnary.machine
  intro bits hbits
  have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat n) bits
      (by simpa only [KS.W19.bitsValue_encodeNat] using hbits.ge)
  simp only [KS.W03.BinaryToUnary.init_eq, KS.W03.BinaryToUnary.cfg,
    KS.W19.bitsValue_encodeNat] at h
  exact h

end KS.W07

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SavedPivotPacketMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.SavedPivotPacket
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers)

theorem full_spec (saved dim row : List Bool) :
    RunSpec program (workspace saved dim row)
      (workspace (KS.W01.frame (payload dim row) ++ saved) [] [])
      (24 * dim.length + 8 * row.length + 22) := by
  have h1 := frame_at dimPorts (workspace saved dim row) dim rfl rfl rfl
  have e1 : Function.update (workspace saved dim row) (dimPorts 1) (KS.W01.frame dim) =
      workspace saved (KS.W01.frame dim) row := by
    funext j; fin_cases j <;> simp [workspace, dimPorts, Function.update]
  rw [e1] at h1
  have h2 := KS.W07.WireAppend.spec (1 : Fin 5) 2 3 (by decide) (by decide) (by decide)
    (workspace saved (KS.W01.frame dim) row) rfl
  have e2 : KS.W07.WireAppend.after 1 2 (workspace saved (KS.W01.frame dim) row) =
      workspace saved [] (payload dim row) := by
    funext j; fin_cases j <;> simp [workspace, payload, KS.W07.WireAppend.after]
  rw [e2] at h2
  have h3 := frame_at packetPorts (workspace saved [] (payload dim row)) (payload dim row) rfl rfl rfl
  have e3 : Function.update (workspace saved [] (payload dim row)) (packetPorts 1)
      (KS.W01.frame (payload dim row)) = workspace saved [] (KS.W01.frame (payload dim row)) := by
    funext j; fin_cases j <;> simp [workspace, packetPorts, Function.update]
  rw [e3] at h3
  have h4 := KS.W07.WireAppend.spec (2 : Fin 5) 0 3 (by decide) (by decide) (by decide)
    (workspace saved [] (KS.W01.frame (payload dim row))) rfl
  have e4 : KS.W07.WireAppend.after 2 0 (workspace saved [] (KS.W01.frame (payload dim row))) =
      workspace (KS.W01.frame (payload dim row) ++ saved) [] [] := by
    funext j; fin_cases j <;> simp [workspace, KS.W07.WireAppend.after]
  rw [e4] at h4
  have h := ((h1.compose h2).compose h3).compose h4
  have ht : (((4 * dim.length + 3) +
      (2 * (workspace saved (KS.W01.frame dim) row 1).length + 2)) +
      (4 * (payload dim row).length + 3)) +
      (2 * (workspace saved [] (KS.W01.frame (payload dim row)) 2).length + 2) =
      24 * dim.length + 8 * row.length + 22 := by
    change (((4 * dim.length + 3) + (2 * (KS.W01.frame dim).length + 2)) +
      (4 * (payload dim row).length + 3)) +
      (2 * (KS.W01.frame (payload dim row)).length + 2) = _
    simp only [payload, List.length_append, KS.W01.length_frame]
    omega
  rw [ht] at h
  exact h

theorem pop_spec (saved dim row : List Bool) :
    RunSpec popProgram (workspace (KS.W01.frame (payload dim row) ++ saved) [] [])
      (workspace saved dim row) (9 * dim.length + 3 * row.length + 7) := by
  have h1 := KS.W11.FrameWireCodec.unframe_spec outerPorts (workspace [] [] [])
    (payload dim row) saved
  have e1 : registers outerPorts (workspace [] [] [])
      (KS.W01.frame (payload dim row) ++ saved) [] [] =
      workspace (KS.W01.frame (payload dim row) ++ saved) [] [] := by
    funext j; fin_cases j <;> simp [registers, outerPorts, workspace]
  have e2 : registers outerPorts (workspace [] [] []) saved (payload dim row) [] =
      workspace saved [] (payload dim row) := by
    funext j; fin_cases j <;> simp [registers, outerPorts, workspace]
  rw [e1, e2] at h1
  have h2 := KS.W11.FrameWireCodec.unframe_spec innerPorts (workspace saved [] []) dim row
  have e3 : registers innerPorts (workspace saved [] []) (KS.W01.frame dim ++ row) [] [] =
      workspace saved [] (payload dim row) := by
    funext j; fin_cases j <;> simp [registers, innerPorts, workspace, payload]
  have e4 : registers innerPorts (workspace saved [] []) row dim [] = workspace saved dim row := by
    funext j; fin_cases j <;> simp [registers, innerPorts, workspace]
  rw [e3, e4] at h2
  have h := h1.compose h2
  have ht : (3 * (payload dim row).length + 2) + (3 * dim.length + 2) =
      9 * dim.length + 3 * row.length + 7 := by
    simp only [payload, List.length_append, KS.W01.length_frame]
    omega
  rw [ht] at h
  exact h

end KS.W08.SavedPivotPacket

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistoryMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem save_spec (saved pd pt cd ct : List Bool) :
    RunSpec saveProgram (state saved pd pt cd ct)
      (state (savedFrame pd pt ++ saved) [] [] cd ct)
      (24 * pd.length + 8 * pt.length + 22) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec
    KS.W08.SavedPivotPacket.program savedPorts
    (KS.W08.SavedPivotPacket.workspace saved pd pt)
    (KS.W08.SavedPivotPacket.workspace (savedFrame pd pt ++ saved) [] [])
    _ _ _ (KS.W08.SavedPivotPacket.full_spec saved pd pt)
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro j hj
    have h32 : j ≠ 32 := by simpa [savedPorts] using hj 0
    have h26 : j ≠ 26 := by simpa [savedPorts] using hj 1
    have h31 : j ≠ 31 := by simpa [savedPorts] using hj 2
    simp [state, h32, h26, h31]

theorem restore_spec (saved pd pt witness : List Bool) :
    RunSpec restoreProgram (state (savedFrame pd pt ++ saved) [] [] [] witness)
      (state saved pd pt [] witness) (9 * pd.length + 3 * pt.length + 7) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec
    KS.W08.SavedPivotPacket.popProgram savedPorts
    (KS.W08.SavedPivotPacket.workspace (savedFrame pd pt ++ saved) [] [])
    (KS.W08.SavedPivotPacket.workspace saved pd pt)
    _ _ _ (KS.W08.SavedPivotPacket.pop_spec saved pd pt)
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro j hj
    have h32 : j ≠ 32 := by simpa [savedPorts] using hj 0
    have h26 : j ≠ 26 := by simpa [savedPorts] using hj 1
    have h31 : j ≠ 31 := by simpa [savedPorts] using hj 2
    simp [state, h32, h26, h31]

theorem descend_spec (saved pd pt cd ct : List Bool) :
    RunSpec descendProgram (state saved pd pt cd ct)
      (state (savedFrame pd pt ++ saved) cd ct [] [])
      (24 * pd.length + 8 * pt.length + 2 * cd.length + 2 * ct.length + 26) := by
  have h1 := save_spec saved pd pt cd ct
  have h2 := KS.W07.WireAppend.spec (23 : Fin 35) 31 33 (by decide) (by decide) (by decide)
    (state (savedFrame pd pt ++ saved) [] [] cd ct) rfl
  have e2 : KS.W07.WireAppend.after 23 31
      (state (savedFrame pd pt ++ saved) [] [] cd ct) =
      state (savedFrame pd pt ++ saved) [] ct cd [] := by
    funext j; fin_cases j <;> simp [state, KS.W07.WireAppend.after]
  rw [e2] at h2
  have h3 := KS.W07.WireAppend.spec (30 : Fin 35) 26 33 (by decide) (by decide) (by decide)
    (state (savedFrame pd pt ++ saved) [] ct cd []) rfl
  have e3 : KS.W07.WireAppend.after 30 26
      (state (savedFrame pd pt ++ saved) [] ct cd []) =
      state (savedFrame pd pt ++ saved) cd ct [] [] := by
    funext j; fin_cases j <;> simp [state, KS.W07.WireAppend.after]
  rw [e3] at h3
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp [descendProgram, state])
  omega

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SchurWitnessHead
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

def fetchPivotProgram : Program 29 := compose copyDimension readProgram

def schurHeadProgram : Program 29 := compose (compose (compose program fetchPivotProgram)
  (StackTransfer.program 17 0 26)) negativeDivisionProgram

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_StoredWitnessLift
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.StoredWitnessLift
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W12.RowDot

def saved {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : Fin 30 → List Bool :=
  fun j => if j = 19 then KS.W08.denseMatrixTape M else if j = 22 then Computability.encodeNat (n + 1)
    else if j = 29 then vectorTape y else []

def work {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ)
    (padded head result : List Bool) : Fin 30 → List Bool :=
  fun j => if j = 20 then padded else if j = 10 then head else if j = 17 then result else saved M y j

def headProgram : Program 30 := KS.W29.FixedSequential.liftPorts schurHeadProgram headPorts

def program : Program 30 := compose (compose (compose (compose (compose
  (copyZeroPadded padPorts) headProgram) (KS.W11.FrameWireCodec.frameProgram framePorts))
  (KS.W01.FixedCopy.program copyPorts)) (KS.W12.StackTransfer.program 10 17 26))
  (KS.W04.BinaryStackMoves.clearProgram 20)

end KS.W12.StoredWitnessLift

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotWitnessMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def liftWitnessProgram : Program 35 := liftPorts KS.W12.StoredWitnessLift.program witnessPorts

def parentState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) :
    Fin 35 → List Bool :=
  state saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) []
    (KS.W12.RowDot.vectorTape y)

theorem schurHead_eq {n : ℕ} (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) :
    Fin.cons (KS.W12.RowDot.schurHead M y) y = schurWitnessLift (DenseRatMatrix.decode M) y := by
  simp [KS.W12.RowDot.schurHead, schurWitnessLift, neg_div]

def witnessCleanup : Program 35 := KS.W04.CleanRationalCompare.clearListProgram 17 [26,31,23]
def replayProgram : Program 35 := compose (compose liftWitnessProgram witnessCleanup)
  (KS.W07.WireAppend.program 17 23 33)

def popReplayProgram : Program 35 := compose restoreProgram replayProgram

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotReplayLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def restoreAllProgram : Program 35 := KS.W29.FixedLoop.loop popReplayProgram replayGuard

def restoreConfig (s : Fin 35 → List Bool) : Config 35 restoreAllProgram.states :=
  ⟨some restoreAllProgram.initial, s⟩

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurCellMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCellMachine

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem preparePair_spec (source target : Fin 23)
    (hst : source ≠ target) (hs16 : source ≠ 16) (ht16 : target ≠ 16)
    (ht0 : target ≠ 0) (before : Fin 23 → List Bool) (he : before 16 = []) :
    RunSpec (preparePair source target) before (pairAfter source target before)
      (4 * (before source).length + 2 * (before target).length + 4) := by
  have h₁ := WireAppend.spec source target 16 hst hs16 (Ne.symm ht16) before he
  have hempty : WireAppend.after source target before 16 = [] := by
    simp [WireAppend.after, Ne.symm hs16, Ne.symm ht16, he]
  have h₂ := WireAppend.spec target 0 16 ht0 ht16 (by decide)
    (WireAppend.after source target before) hempty
  have h := h₁.compose h₂
  have hlen : (WireAppend.after source target before target).length =
      (before source).length + (before target).length := by
    simp [WireAppend.after, Ne.symm hst]
  simpa only [preparePair, pairAfter, hlen, Nat.mul_add,
    show 2 * (before source).length + 2 +
      (2 * (before source).length + 2 * (before target).length + 2) =
      4 * (before source).length + 2 * (before target).length + 4 by omega] using h

def multiply : Program 23 := KS.W29.FixedSequential.liftPorts
  KS.W15.RationalMultiply.program (firstPorts 13 (by decide))
def divide : Program 23 := KS.W29.FixedSequential.liftPorts
  KS.W30.RationalDivision.program (firstPorts 15 (by decide))
def subtract : Program 23 := KS.W29.FixedSequential.liftPorts
  KS.W13.RationalSubtract.program (firstPorts 19 (by decide))

def program : Program 23 := compose (preparePair 20 21)
  (compose multiply (compose (preparePair 10 22)
    (compose divide (compose (preparePair 19 10) subtract))))

theorem prepare_product_spec (x a b c : List Bool) :
    RunSpec (preparePair 20 21) (workspace [] [] x a b c)
      (workspace (a ++ b) [] x [] [] c) (4 * a.length + 2 * b.length + 4) := by
  have h := preparePair_spec 20 21 (by decide) (by decide) (by decide) (by decide)
    (workspace [] [] x a b c) rfl
  have he : pairAfter 20 21 (workspace [] [] x a b c) = workspace (a ++ b) [] x [] [] c := by
    funext j; fin_cases j <;> simp [pairAfter, WireAppend.after, workspace]
  rw [he] at h
  exact h

theorem prepare_division_spec (x p c : List Bool) :
    RunSpec (preparePair 10 22) (workspace [] p x [] [] c)
      (workspace (p ++ c) [] x [] [] []) (4 * p.length + 2 * c.length + 4) := by
  have h := preparePair_spec 10 22 (by decide) (by decide) (by decide) (by decide)
    (workspace [] p x [] [] c) rfl
  have he : pairAfter 10 22 (workspace [] p x [] [] c) = workspace (p ++ c) [] x [] [] [] := by
    funext j; fin_cases j <;> simp [pairAfter, WireAppend.after, workspace]
  rw [he] at h
  exact h

theorem prepare_subtraction_spec (x q : List Bool) :
    RunSpec (preparePair 19 10) (workspace [] q x [] [] [])
      (workspace (x ++ q) [] [] [] [] []) (4 * x.length + 2 * q.length + 4) := by
  have h := preparePair_spec 19 10 (by decide) (by decide) (by decide) (by decide)
    (workspace [] q x [] [] []) rfl
  have he : pairAfter 19 10 (workspace [] q x [] [] []) = workspace (x ++ q) [] [] [] [] [] := by
    funext j; fin_cases j <;> simp [pairAfter, WireAppend.after, workspace]
  rw [he] at h
  exact h

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurTableInvariant
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07.SchurTable

open KS.W08 KS.W17

theorem entry_parts_le {n : ℕ} (M : DenseRatMatrix (n + 1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (i j : Fin n) :
    (schurTail (DenseRatMatrix.decode M) i j).num.natAbs ≤ 2 ^ (4 * b + 3) ∧
      (schurTail (DenseRatMatrix.decode M) i j).den ≤ 2 ^ (4 * b + 3) := by
  have hb : (schurEntryExpr (DenseRatMatrix.decode M) i j).inputsBounded b :=
    ⟨⟨hnum _ _, hden _ _⟩, ⟨⟨⟨hnum _ _, hden _ _⟩, ⟨hnum _ _, hden _ _⟩⟩,
      ⟨hnum _ _, hden _ _⟩⟩⟩
  have h := (schurEntryExpr (DenseRatMatrix.decode M) i j).eval_parts_le b hb
  simp [schurEntryExpr, RationalExpr.leaves, RationalExpr.operations] at h
  exact h

end KS.W07.SchurTable

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurCounters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCounters

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

theorem push_spec {k : ℕ} (port : Fin k) (bit : Bool) (before : Fin k → List Bool) :
    RunSpec (pushProgram port bit) before
      (Function.update before port (bit :: before port)) 1 := by
  intro bits hlen
  cases bits with
  | nil => simp at hlen
  | cons coin rest =>
    have hr : rest = [] := by
      apply List.length_eq_zero_iff.mp
      simpa using hlen
    subst rest
    change (compile (0 : Fin 1) port port (pushDispatch port bit)).step
      ⟨some (0 : Fin 1), before⟩ coin = _
    erw [step_compile]
    apply congrArg₂ Config.mk
    · rfl
    · funext j
      by_cases hj : j = port
      · subst j
        simp [pushDispatch, Instruction.action, KS.W29.StackAction.apply]
      · simp [pushDispatch, Instruction.action, KS.W29.StackAction.apply, hj]

def incrementProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (pushProgram (ports 0) true) (KS.W13.RationalAdd.canonicalAddProgram ports)

theorem increment_spec {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (before : Fin k → List Bool) (n : ℕ)
    (hzero : before (ports 0) = []) (hcounter : before (ports 1) = Computability.encodeNat n)
    (hscratch : before (ports 2) = []) :
    RunSpec (incrementProgram ports) before
      (Function.update before (ports 1) (Computability.encodeNat (n + 1)))
      (2 * (Computability.encodeNat n).length + 6) := by
  have h01 : ports 0 ≠ ports 1 := ports.injective.ne (by decide)
  have h02 : ports 0 ≠ ports 2 := ports.injective.ne (by decide)
  have h12 : ports 1 ≠ ports 2 := ports.injective.ne (by decide)
  have hp := push_spec (ports 0) true before
  have hstart : Function.update before (ports 0) (true :: before (ports 0)) =
      registers ports before [true] (Computability.encodeNat n) [] := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      fin_cases i <;> simp [hzero, hcounter, hscratch, Ne.symm h01, Ne.symm h02]
    · have hn : ∀ i, j ≠ ports i := by simpa using hj
      rw [registers_other _ _ _ _ _ _ hn]
      simp [Function.update_of_ne (hn 0)]
  rw [hstart] at hp
  have ha := KS.W13.RationalAdd.canonicalAdd_spec ports before [true]
    (Computability.encodeNat n)
  have hresult : KS.W13.RationalAdd.addResult [true] (Computability.encodeNat n) =
      Computability.encodeNat (n + 1) := by
    simp [KS.W13.RationalAdd.addResult, KS.W19.bitsValue_encodeNat, KS.W19.bitsValue, Nat.add_comm]
  have hend : registers ports before []
      (KS.W13.RationalAdd.addResult [true] (Computability.encodeNat n)) [] =
      Function.update before (ports 1) (Computability.encodeNat (n + 1)) := by
    rw [hresult]
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      fin_cases i <;> simp [hzero, hscratch, h01, Ne.symm h12]
    · have hn : ∀ i, j ≠ ports i := by simpa using hj
      rw [registers_other _ _ _ _ _ _ hn]
      simp [Function.update_of_ne (hn 1)]
  have h := hp.compose ha
  rw [hend] at h
  have ht := KS.W13.RationalAdd.canonicalAddTicks_le [true] (Computability.encodeNat n)
  apply h.mono
  simp only [List.length_singleton] at ht
  omega

end KS.W07.SchurCounters

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurDimension
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07.SchurDimension
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurReadStage

def predecessor : Program 32 := compose
  (copyProgram 26 0 (by decide) (by decide) (by decide))
  (compose (SchurCounters.pushProgram 1 true)
    (compose (KS.W01.SignedSerializePrimitives.subtractProgram predecessorPorts)
      (WireAppend.program 1 30 16)))

theorem predecessor_spec (s : Fin 32 → List Bool) (n : ℕ)
    (hd : s 26 = Computability.encodeNat (n+1))
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h16 : s 16 = []) (h30 : s 30 = []) :
    RunSpec predecessor s (Function.update s 30 (Computability.encodeNat n)) (predecessorTicks n) := by
  have hc := copy_spec 26 0 (by decide) (by decide) (by decide) s h0 h16
  rw [hd] at hc
  have hp := SchurCounters.push_spec (1 : Fin 32) true
    (Function.update s 0 (Computability.encodeNat (n+1)))
  have hs := KS.W01.SignedSerializePrimitives.decrement_spec predecessorPorts s
    (Computability.encodeNat (n+1))
  rw [KS.W01.WireMagnitude.decrement_encode_succ] at hs
  have hi : Function.update (Function.update s 0 (Computability.encodeNat (n+1))) 1
      (true :: (Function.update s 0 (Computability.encodeNat (n+1))) 1) =
      KS.W28.FixedPositiveSerializer.registers predecessorPorts s
        (Computability.encodeNat (n+1)) [true] [] := by
    funext j; fin_cases j <;> simp [KS.W28.FixedPositiveSerializer.registers,predecessorPorts,h1,h2]
  rw [hi] at hp
  have ho : KS.W28.FixedPositiveSerializer.registers predecessorPorts s []
      (Computability.encodeNat n) [] = Function.update s 1 (Computability.encodeNat n) := by
    funext j; fin_cases j <;> simp [KS.W28.FixedPositiveSerializer.registers,predecessorPorts,h0,h2]
  rw [ho] at hs
  have hm := WireAppend.spec (1 : Fin 32) 30 16 (by decide) (by decide) (by decide)
    (Function.update s 1 (Computability.encodeNat n)) (by simpa using h16)
  have hout : WireAppend.after 1 30 (Function.update s 1 (Computability.encodeNat n)) =
      Function.update s 30 (Computability.encodeNat n) := by
    funext j; fin_cases j <;> simp [WireAppend.after,h1,h30]
  rw [hout] at hm
  exact hc.compose (hp.compose (hs.compose hm))

theorem unary_spec (column : Bool) (s : Fin 32 → List Bool) (n : ℕ)
    (hd : s 30 = Computability.encodeNat n)
    (h0 : s 0 = []) (h1 : s 1 = []) (h16 : s 16 = []) (ht : s (counterPort column) = []) :
    RunSpec (unaryProgram column) s
      (Function.update s (counterPort column) (List.replicate n true))
      (4*n + 6*(Computability.encodeNat n).length+4) := by
  have hc := copy_spec 30 0 (by decide) (by decide) (by decide) s h0 h16
  rw [hd] at hc
  have hsmall : RunSpec KS.W03.BinaryToUnary.program
      ![Computability.encodeNat n,[],[]] ![[],List.replicate n true,[]]
      (4*n + 4*(Computability.encodeNat n).length+2) := KS.W07.canonicalUnary_spec n
  have hu : RunSpec (liftPorts KS.W03.BinaryToUnary.program (unaryPorts column))
      (Function.update s 0 (Computability.encodeNat n))
      (Function.update s (counterPort column) (List.replicate n true))
      (4*n + 4*(Computability.encodeNat n).length+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ (unaryPorts column) _ _ _ _ _ hsmall
    · intro j; fin_cases j <;> cases column <;> simp_all [counterPort]
    · intro j; fin_cases j <;> cases column <;> simp_all [counterPort]
    · intro j hj
      have hzero := hj 0
      have htarget := hj 1
      change j ≠ 0 at hzero
      change j ≠ counterPort column at htarget
      simp [Function.update_of_ne,hzero,htarget]
  have h := hc.compose hu
  have he : (2*(Computability.encodeNat n).length+2) +
      (4*n+4*(Computability.encodeNat n).length+2) = 4*n+6*(Computability.encodeNat n).length+4 := by omega
  simpa only [unaryProgram,he] using h

end KS.W07.SchurDimension

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurOperands
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07.SchurOperands
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurReadStage

def collect : Program 32 := compose (SchurReadStage.program true true 0)
  (compose (SchurReadStage.program true false 1)
    (compose (SchurReadStage.program false true 2) (SchurReadStage.program false false 3)))

def readBudget {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ) (i j : Fin n)
    (s : Fin 32 → List Bool) : ℕ :=
  let x := DenseRatMatrix.decode M i.succ j.succ
  let a := DenseRatMatrix.decode M i.succ 0
  let b := DenseRatMatrix.decode M 0 j.succ
  let c := DenseRatMatrix.decode M 0 0
  let t (row col : Bool) (q : ℚ) := prepareTicks s row col +
    (1024*(n+2)^2*(B+1) + (2*KS.W01.ratLength q+2))
  t true true x + (t true false a + (t false true b + t false false c))

def scalar : Program 32 := liftPorts SchurCellMachine.program scalarPorts

def program : Program 32 := compose collect scalar

end KS.W07.SchurOperands

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurEntryMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurEntryMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem append_spec (s : Fin 32 → List Bool) (h0 : s 0 = []) (h1 : s 1 = [])
    (h10 : s 10 = []) (q : ℚ) :
    RunSpec appendProgram (Function.update s 10 (KS.W01.encodeRat q))
      (Function.update s 23 ((KS.W01.frame (KS.W01.encodeRat q)).reverse ++ s 23))
      (6*KS.W01.ratLength q+5) := by
  have hf := KS.W11.FrameWireCodec.frame_rat_spec framePorts s q
  have hi : KS.W28.FixedPositiveSerializer.registers framePorts s [] (KS.W01.encodeRat q) [] =
      Function.update s 10 (KS.W01.encodeRat q) := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,h0,h1]
  have ho : KS.W28.FixedPositiveSerializer.registers framePorts s []
      (KS.W01.frame (KS.W01.encodeRat q)) [] =
      Function.update s 10 (KS.W01.frame (KS.W01.encodeRat q)) := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,h0,h1]
  rw [hi,ho] at hf
  have hm := KS.W15.RationalMultiply.move_spec (10 : Fin 32) 23 (by decide)
    (Function.update s 10 (KS.W01.frame (KS.W01.encodeRat q)))
  have hout : KS.W15.RationalMultiply.moveAfter 10 23
      (Function.update s 10 (KS.W01.frame (KS.W01.encodeRat q))) =
      Function.update s 23 ((KS.W01.frame (KS.W01.encodeRat q)).reverse ++ s 23) := by
    funext j; fin_cases j <;> simp [KS.W15.RationalMultiply.moveAfter,h10]
  rw [hout] at hm
  have h := hf.compose hm
  have ht : (4*(KS.W01.encodeRat q).length+3) +
      (KS.W01.frame (KS.W01.encodeRat q)).length+1 = 6*KS.W01.ratLength q+5 := by
    rw [KS.W01.length_frame]; unfold KS.W01.ratLength; omega
  simpa only [appendProgram,Function.update_self,←Nat.add_assoc,ht] using h

def program : Program 32 := compose SchurOperands.program appendProgram

theorem finish_spec (s : Fin 32 → List Bool) (wire : List Bool)
    (h23 : s 23 = wire.reverse) (h0 : s 0 = []) (h16 : s 16 = []) :
    RunSpec finishProgram s (Function.update s 23 wire) (3*wire.length+3) := by
  have hm := KS.W15.RationalMultiply.move_spec (23 : Fin 32) 0 (by decide) s
  let mid := KS.W15.RationalMultiply.moveAfter 23 0 s
  have hm0 : mid 0 = wire := by simp [mid,KS.W15.RationalMultiply.moveAfter,h23,h0]
  have hm23 : mid 23 = [] := by rfl
  have hm16 : mid 16 = [] := by simpa [mid,KS.W15.RationalMultiply.moveAfter] using h16
  have ha := WireAppend.spec (0 : Fin 32) 23 16 (by decide) (by decide) (by decide) mid hm16
  have hout : WireAppend.after 0 23 mid = Function.update s 23 wire := by
    funext j; fin_cases j <;> simp [WireAppend.after,mid,KS.W15.RationalMultiply.moveAfter,h23,h0]
  rw [hout,hm0] at ha
  have h := hm.compose ha
  have ht : (s 23).length+1+(2*wire.length+2) = 3*wire.length+3 := by
    rw [h23,List.length_reverse]; omega
  simpa only [finishProgram,ht] using h

end KS.W07.SchurEntryMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurTableMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def columnBody : Program 32 := compose SchurEntryMachine.program
  (SchurCounters.incrementProgram columnIncrementPorts)

def columnLoop : Program 32 := KS.W29.FixedLoop.loop columnBody (guard 25)

def rowBody : Program 32 := compose (SchurDimension.unaryProgram true)
  (compose (SchurCounters.pushProgram 28 true)
    (compose columnLoop (compose (KS.W04.BinaryStackMoves.clearProgram 28)
      (SchurCounters.incrementProgram rowIncrementPorts))))

def rowLoop : Program 32 := KS.W29.FixedLoop.loop rowBody (guard 24)

def «initialize_» : Program 32 := compose SchurDimension.predecessor
  (compose (SchurDimension.unaryProgram false) (SchurCounters.pushProgram 27 true))

def program : Program 32 := compose «initialize_» (compose rowLoop finish)

def inputState {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else
    if j=26 then Computability.encodeNat (n+1) else []

def outputState {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else
    if j=26 then Computability.encodeNat (n+1) else
    if j=30 then Computability.encodeNat n else
    if j=23 then KS.W08.denseMatrixTape
      (DenseRatMatrix.ofMatrix (KS.W17.schurTail (DenseRatMatrix.decode M))) else []

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SchurLoopState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem prefix_complete {n : ℕ} (M : DenseRatMatrix (n+1)) :
    «prefix» M (n*n) = KS.W08.denseMatrixTape (tailMatrix M) := by
  simp only [«prefix»,KS.W08.denseMatrixTape]
  rw [List.take_of_length_le (KS.W08.denseMatrixPayloads_length (tailMatrix M)).le]

theorem prefix_step {n : ℕ} (M : DenseRatMatrix (n+1)) (i j : Fin n) :
    «prefix» M (i.val*n+j.val+1) = «prefix» M (i.val*n+j.val) ++
      KS.W01.frame (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j)) := by
  unfold «prefix»
  rw [List.take_succ_eq_append_getElem (by
    rw [KS.W08.denseMatrixPayloads_length]
    exact KS.W08.matrixEntryIndex_lt i j),List.flatMap_append]
  rw [KS.W08.denseMatrixPayloads_get]
  simp [tailMatrix]

def columnState {n : ℕ} (M : DenseRatMatrix (n+1)) (r c rows cols : ℕ) : Fin 32 → List Bool :=
  fun j => if j=23 then («prefix» M (r*n+c)).reverse else
    if j=24 then List.replicate rows true else
    if j=25 then List.replicate cols true else
    if j=26 then Computability.encodeNat (n+1) else
    if j=27 then Computability.encodeNat (r+1) else
    if j=28 then Computability.encodeNat (c+1) else
    if j=30 then Computability.encodeNat n else
    if j=31 then KS.W08.denseMatrixTape M else []

def rowState {n : ℕ} (M : DenseRatMatrix (n+1)) (r rows : ℕ) : Fin 32 → List Bool :=
  fun j => if j=23 then («prefix» M (r*n)).reverse else
    if j=24 then List.replicate rows true else
    if j=26 then Computability.encodeNat (n+1) else
    if j=27 then Computability.encodeNat (r+1) else
    if j=30 then Computability.encodeNat n else
    if j=31 then KS.W08.denseMatrixTape M else []

theorem column_workClear {n : ℕ} (M : DenseRatMatrix (n+1)) (r c rows cols : ℕ) :
    SchurReadStage.WorkClear (columnState M r c rows cols) := by
  intro j hj
  have h23 : j≠23 := by intro h; subst j; omega
  have h24 : j≠24 := by intro h; subst j; omega
  have h25 : j≠25 := by intro h; subst j; omega
  have h26 : j≠26 := by intro h; subst j; omega
  have h27 : j≠27 := by intro h; subst j; omega
  have h28 : j≠28 := by intro h; subst j; omega
  have h30 : j≠30 := by intro h; subst j; omega
  have h31 : j≠31 := by intro h; subst j; omega
  simp [columnState,h23,h24,h25,h26,h27,h28,h30,h31]

theorem column_pop {n : ℕ} (M : DenseRatMatrix (n+1)) (r c rows cols : ℕ) :
    Function.update (columnState M r c rows (cols+1)) 25 (List.replicate cols true) =
      columnState M r c rows cols := by
  funext k; fin_cases k <;> rfl

theorem row_pop {n : ℕ} (M : DenseRatMatrix (n+1)) (r rows : ℕ) :
    Function.update (rowState M r (rows+1)) 24 (List.replicate rows true) = rowState M r rows := by
  funext k; fin_cases k <;> rfl

end KS.W07.SchurLoopState

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurRowLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem rowTicks_le {n : ℕ} (B : ℕ) (i : Fin n) : rowTicks n B i.val ≤ rowBudget n B := by
  have rawLength (t : ℕ) : (Computability.encodeNat t).length ≤ t := by
    change KS.W01.natPayloadLength t ≤ t
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have ln := rawLength n
  have ln' := rawLength (n+1)
  have li : (Computability.encodeNat (i.val+1)).length ≤ n+1 :=
    (rawLength (i.val+1)).trans (by omega)
  unfold rowTicks rowBudget
  omega

end KS.W07.SchurLoopState

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurTableCorrectness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurLoopState

theorem initialize_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    RunSpec «initialize_» (inputState M) (rowState M 0 n) (initializeTicks n) := by
  let s := inputState M
  let d := Function.update s 30 (Computability.encodeNat n)
  let u := Function.update d 24 (List.replicate n true)
  have hd := SchurDimension.predecessor_spec s n rfl rfl rfl rfl rfl rfl
  have hu := SchurDimension.unary_spec false d n rfl rfl rfl rfl rfl
  have hp := SchurCounters.push_spec (27 : Fin 32) true u
  have hone : Computability.encodeNat 1 = [true] := by decide
  have hout : Function.update u 27 (true::u 27) = rowState M 0 n := by
    funext k; fin_cases k <;> simp [u,d,s,inputState,rowState,hone]
  rw [hout] at hp
  exact hd.compose (hu.compose hp)

theorem initializeTicks_le (n : ℕ) : initializeTicks n ≤ 30*(n+2) := by
  have ln : (Computability.encodeNat n).length ≤ n := by
    change KS.W01.natPayloadLength n ≤ n
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have ld : (Computability.encodeNat (n+1)).length ≤ n+1 := by
    change KS.W01.natPayloadLength (n+1) ≤ n+1
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  unfold initializeTicks SchurDimension.predecessorTicks
  omega

def finishTicks {n : ℕ} (M : DenseRatMatrix (n+1)) : ℕ :=
  ((Computability.encodeNat (n+1)).length+1) +
    (3*(KS.W08.denseMatrixTape (tailMatrix M)).length+3)

theorem finish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    RunSpec finish (rowState M n 0) (outputState M) (finishTicks M) := by
  let mid := Function.update (rowState M n 0) 27 []
  have hc := KS.W15.RationalMultiply.clear_spec (27 : Fin 32) (rowState M n 0)
  have hclearState : KS.W15.RationalMultiply.clearAfter 27 (rowState M n 0) = mid := by
    funext k
    by_cases hk : k=27 <;> simp [KS.W15.RationalMultiply.clearAfter,mid,hk]
  rw [hclearState] at hc
  have hr := SchurEntryMachine.finish_spec mid (KS.W08.denseMatrixTape (tailMatrix M))
    (by simp [mid,rowState,prefix_complete]) rfl rfl
  have hout : Function.update mid 23 (KS.W08.denseMatrixTape (tailMatrix M)) = outputState M := by
    funext k; fin_cases k <;> simp [mid,rowState,outputState,tailMatrix]
  rw [hout] at hr
  exact hc.compose hr

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotDescentMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def schurProgram : Program 35 := liftPorts KS.W07.SchurTableMachine.program schurPorts

def fullDescendProgram : Program 35 := compose schurProgram descendProgram

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowRead
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowRead
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

def program : Program 32 := compose
  (compose (copyProgram 28 0 (by decide) (by decide) (by decide))
    (copyProgram 26 2 (by decide) (by decide) (by decide))) reader

end KS.W17.PivotRowRead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowClassify
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowClassify
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

def classifier : Program 32 := liftPorts KS.W06.RationalSignClassifier.program classifierPorts

def program : Program 32 := compose (compose PivotRowRead.program classifier)
  (KS.W07.WireAppend.program 9 29 16)

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) (j : Fin (n+1)) : ℕ :=
  ((2*(Computability.encodeNat j.val).length+2) +
    (2*(Computability.encodeNat (n+1)).length+2) + 1024*(n+2)^2*(b+1)) +
  256*(KS.W01.ratLength (DenseRatMatrix.decode M 0 j)+1) +
  (2*(KS.W06.RationalSignClassifier.outputCode (DenseRatMatrix.decode M 0 j)).length+2)

end KS.W17.PivotRowClassify

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowBody
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowBody
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

def zeroProgram : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  (SchurCounters.incrementProgram incrementPorts)
def foundProgram : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  (SchurCounters.pushProgram 24 true)
def branch : Program 32 := KS.W29.FixedBranch.branch zeroProgram foundProgram 24 select

theorem branch_spec (before : Fin 32 → List Bool) (q : ℚ) (idx : ℕ)
    (h0 : before 0 = []) (h1 : before 1 = []) (hf : before 24 = [])
    (hj : before 28 = Computability.encodeNat idx) (h29 : before 29 = []) :
    RunSpec branch (Function.update before 29 (KS.W06.RationalSignClassifier.outputCode q))
      (after before q idx) (2*(Computability.encodeNat idx).length+10) := by
  let s := Function.update before 29 (KS.W06.RationalSignClassifier.outputCode q)
  have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 32) s
  have he : KS.W04.CleanRationalCompare.clearState 29 s = before := by
    funext j
    by_cases hjj : j = 29 <;> simp [KS.W04.CleanRationalCompare.clearState, s, hjj, h29]
  rw [he] at hc
  by_cases hz : q = 0
  · have hinc := SchurCounters.increment_spec incrementPorts before idx h0 hj h1
    have hb := hc.compose hinc
    have hs : ∀ coin, select (observedHeads (Config.mk (some (KS.W29.FixedBranch.start zeroProgram foundProgram)) s)) coin =
        ⟨.left, Vector.ofFn (fun _ => .stay)⟩ := by
      intro coin
      subst q
      simp [select, s, KS.W06.RationalSignClassifier.outputCode, observedHeads, KS.W29.topCode]
    have hbranch := KS.W06.RationalCompare.branch_spec_left zeroProgram foundProgram 24 select s _ _ hs hb
    change RunSpec branch s (after before q idx) _
    rw [after, ite_eq_left hz]
    apply hbranch.mono
    simp [s, hz, KS.W06.RationalSignClassifier.outputCode]
    omega
  · have hp := SchurCounters.push_spec (24 : Fin 32) true before
    rw [hf] at hp
    have hb := hc.compose hp
    have hs : ∀ coin, select (observedHeads (Config.mk (some (KS.W29.FixedBranch.start zeroProgram foundProgram)) s)) coin =
        ⟨.right, Vector.ofFn (fun _ => .stay)⟩ := by
      intro coin
      by_cases hn : q < 0 <;>
        simp [select, s, KS.W06.RationalSignClassifier.outputCode, hn, hz, observedHeads, KS.W29.topCode]
    have hbranch := KS.W06.RationalCompare.branch_spec_right zeroProgram foundProgram 24 select s _ _ hs hb
    simp only [after, hz, ite_false, if_false]
    change RunSpec branch s (Function.update before 24 [true]) _
    apply hbranch.mono
    by_cases hn : q < 0 <;> simp [s, KS.W06.RationalSignClassifier.outputCode, hn, hz]

def program : Program 32 := compose PivotRowClassify.program branch

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) (j : Fin (n+1)) : ℕ :=
  PivotRowClassify.ticks M b j + (2*(Computability.encodeNat j.val).length+10)

end KS.W17.PivotRowBody

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def outcome {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) : ℕ → Outcome
  | 0 => ⟨a,0,false⟩
  | k+1 => if entry M a = 0 then outcome M (a+1) k else ⟨a,k,true⟩

def program : Program 32 := KS.W29.FixedLoop.loop PivotRowBody.program guard

def config (s : Fin 32 → List Bool) : Config 32 program.states := ⟨some program.initial,s⟩

def entryTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (b a : ℕ) : ℕ :=
  if h : a < n+1 then PivotRowBody.ticks M b ⟨a,h⟩ else 0

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b a : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => 1 + entryTicks M b a + if entry M a = 0 then ticks M b (a+1) k else 1

theorem step_empty {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) (coin : Bool) :
    program.toMachine.step (config (state M a 0 false)) coin = ⟨none,state M a 0 false⟩ := by
  change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState PivotRowBody.program),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads, KS.W29.topCode]; rfl
  · funext j; simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads,
      KS.W29.topCode, Instruction.action, KS.W29.StackAction.apply]

theorem step_found {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) (coin : Bool) :
    program.toMachine.step (config (state M a k true)) coin = ⟨none,state M a k true⟩ := by
  change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState PivotRowBody.program),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads, KS.W29.topCode]; rfl
  · funext j; simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads,
      KS.W29.topCode, Instruction.action, KS.W29.StackAction.apply]

theorem step_call {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) (coin : Bool) :
    program.toMachine.step (config (state M a (k+1) false)) coin =
      KS.W29.FixedLoop.liftBody PivotRowBody.program
        ⟨some PivotRowBody.program.initial,state M a k false⟩ := by
  change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState PivotRowBody.program),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, guard, state,
      observedHeads, KS.W29.topCode, List.replicate_succ]
  · funext j
    by_cases hj : j=25 <;>
      simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads,
        KS.W29.topCode, Instruction.action, KS.W29.StackAction.apply, List.replicate_succ, hj]

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowInitialize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def «initialize_» : Program 32 := compose
  (compose (compose SchurDimension.predecessor (SchurDimension.unaryProgram true))
    (KS.W04.BinaryStackMoves.clearProgram 30)) (SchurCounters.pushProgram 28 true)

theorem initialize_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    RunSpec «initialize_» (initial M) (state M 1 n false) (initializeTicks n) := by
  let s := initial M
  let t := Function.update s 30 (Computability.encodeNat n)
  let u := Function.update t 25 (List.replicate n true)
  have h1 := SchurDimension.predecessor_spec s n rfl rfl rfl rfl rfl rfl
  have h2 := SchurDimension.unary_spec true t n rfl rfl rfl rfl rfl
  have h3 := KS.W04.CleanRationalCompare.clear_spec (30 : Fin 32) u
  have he : KS.W04.CleanRationalCompare.clearState 30 u = state M 0 n false := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,u,t,s,initial,state,Function.update]
  rw [he] at h3
  have h4 := SchurCounters.push_spec (28 : Fin 32) true (state M 0 n false)
  have he4 : Function.update (state M 0 n false) 28 (true :: state M 0 n false 28) =
      state M 1 n false := by
    funext j; fin_cases j <;> simp [state,Function.update,Computability.encodeNat,Computability.encodeNum,Computability.encodePosNum]
  rw [he4] at h4
  exact ((h1.compose h2).compose h3).compose h4

def offDiagonalProgram : Program 32 := compose «initialize_» program

end KS.W17.PivotRowLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowFinish
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def foundFinish : Program 32 := compose
  (compose (KS.W04.BinaryStackMoves.clearProgram 25) (WireAppend.program 28 30 16))
  (WireAppend.program 24 29 16)
def emptyFinish : Program 32 := KS.W04.CleanRationalCompare.clearListProgram 29 [25,28,24]
def finish : Program 32 := KS.W29.FixedBranch.branch foundFinish emptyFinish 29 finishSelect

def finished {n : ℕ} (M : DenseRatMatrix (n+1)) (idx : ℕ) (found : Bool) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else if j=26 then Computability.encodeNat (n+1) else
    if j=30 then if found then Computability.encodeNat idx else [] else
    if j=29 then if found then [true] else [] else []

theorem foundFinish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (idx k : ℕ) :
    RunSpec foundFinish (state M idx k true) (finished M idx true)
      (k+1+(2*(Computability.encodeNat idx).length+2)+4) := by
  have h1 := KS.W04.CleanRationalCompare.clear_spec (25 : Fin 32) (state M idx k true)
  have he1 : KS.W04.CleanRationalCompare.clearState 25 (state M idx k true) = state M idx 0 true := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,state]
  rw [he1] at h1
  have h2 := WireAppend.spec (28 : Fin 32) 30 16 (by decide) (by decide) (by decide)
    (state M idx 0 true) rfl
  let t := WireAppend.after 28 30 (state M idx 0 true)
  have h3 := WireAppend.spec (24 : Fin 32) 29 16 (by decide) (by decide) (by decide) t rfl
  have he3 : WireAppend.after 24 29 t = finished M idx true := by
    funext j; fin_cases j <;> simp [WireAppend.after,t,state,finished]
  rw [he3] at h3
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp [foundFinish,state,t,WireAppend.after])

theorem emptyFinish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (idx k : ℕ) :
    RunSpec emptyFinish (state M idx k false) (finished M idx false)
      (k+(Computability.encodeNat idx).length+4) := by
  have h := KS.W04.CleanRationalCompare.clearList_spec (29 : Fin 32) [25,28,24] (state M idx k false)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearListState_apply,state,finished]
  · simp [KS.W04.CleanRationalCompare.clearListTicks,KS.W04.CleanRationalCompare.clearState,state]
    omega

theorem finish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (idx k : ℕ) (found : Bool) :
    RunSpec finish (state M idx k found) (finished M idx found) (finishTicks idx k) := by
  cases found
  · have hs : ∀ coin, finishSelect (observedHeads
        (⟨some (KS.W29.FixedBranch.start foundFinish emptyFinish),state M idx k false⟩ :
          Config 32 (foundFinish.states+emptyFinish.states+1))) coin =
        ⟨.right,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin; simp [finishSelect,state,observedHeads,KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    apply (KS.W06.RationalCompare.branch_spec_right foundFinish emptyFinish 29 finishSelect _ _ _ hs
      (emptyFinish_spec M idx k)).mono
    unfold finishTicks
    omega
  · have hs : ∀ coin, finishSelect (observedHeads
        (⟨some (KS.W29.FixedBranch.start foundFinish emptyFinish),state M idx k true⟩ :
          Config 32 (foundFinish.states+emptyFinish.states+1))) coin =
        ⟨.left,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin; simp [finishSelect,state,observedHeads,KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    apply (KS.W06.RationalCompare.branch_spec_left foundFinish emptyFinish 29 finishSelect _ _ _ hs
      (foundFinish_spec M idx k)).mono
    unfold finishTicks
    omega

def completeProgram : Program 32 := compose offDiagonalProgram finish

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotDecision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def zeroProgram : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  PivotRowLoop.completeProgram
def returnProgram : Program 32 := KS.W04.CleanRationalCompare.haltProgram 29

def dispatch : Program 32 := KS.W29.FixedBranch.branch zeroProgram returnProgram 29 select

def program : Program 32 := compose PivotRowClassify.program dispatch

def result {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool :=
  if DenseRatMatrix.decode M 0 0 = 0 then
    PivotRowLoop.finished M (PivotRowLoop.outcome M 1 n).index (PivotRowLoop.outcome M 1 n).found
  else Function.update (PivotRowLoop.initial M) 29
    (KS.W06.RationalSignClassifier.outputCode (DenseRatMatrix.decode M 0 0))

def rowTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) : ℕ :=
  PivotRowLoop.initializeTicks n + PivotRowLoop.ticks M b 1 n +
    PivotRowLoop.finishTicks (PivotRowLoop.outcome M 1 n).index (PivotRowLoop.outcome M 1 n).remaining

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) : ℕ :=
  PivotRowClassify.ticks M b 0 + if DenseRatMatrix.decode M 0 0 = 0 then 3+rowTicks M b else 2

end KS.W17.PivotDecision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowCorrectness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W07

theorem foundIndex_outcome {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) :
    foundIndex (outcome M a k) =
      (List.range' a k).find? (fun i => decide (entry M i ≠ 0)) := by
  induction k generalizing a with
  | zero => simp [outcome,foundIndex]
  | succ k ih =>
    by_cases hz : entry M a = 0
    · simp only [outcome, hz, ite_true, if_true]
      rw [ih]
      simp [List.range'_succ, hz]
    · simp [outcome, hz, foundIndex, List.range'_succ]

theorem offDiagonal_outcome {n : ℕ} (M : DenseRatMatrix (n+1)) :
    foundIndex (outcome M 1 n) =
      (firstNonzeroOffDiagonal (DenseRatMatrix.decode M)).map (fun j => j.succ.val) := by
  rw [foundIndex_outcome,← successor_finRange]
  rw [List.find?_map]
  congr 1
  unfold firstNonzeroOffDiagonal
  congr 1
  funext j
  have hj : j.succ.val < n+1 := j.succ.isLt
  have he : (⟨j.succ.val, hj⟩ : Fin (n+1)) = j.succ := Fin.ext rfl
  change decide (entry M j.succ.val ≠ 0) = decide (DenseRatMatrix.decode M 0 j.succ ≠ 0)
  simp only [entry, dite_eq_left hj, he]

theorem outcome_bounds {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) :
    a ≤ (outcome M a k).index ∧ (outcome M a k).index ≤ a+k ∧
      (outcome M a k).remaining ≤ k := by
  induction k generalizing a with
  | zero => simp [outcome]
  | succ k ih =>
    by_cases hz : entry M a = 0
    · have h := ih (a+1)
      simp only [outcome,hz,ite_true, if_true]
      omega
    · simp [outcome,hz]

end KS.W17.PivotRowLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionCorrectness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotDecision
open KS.W07

theorem noIndex {n : ℕ} (M : DenseRatMatrix (n+1))
    (h : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = none) :
    (PivotRowLoop.outcome M 1 n).found = false := by
  have he := PivotRowLoop.offDiagonal_outcome M
  rw [h] at he
  cases hf : (PivotRowLoop.outcome M 1 n).found
  · rfl
  · simp [PivotRowLoop.foundIndex,hf] at he

theorem result_nonterminal {n : ℕ} (M : DenseRatMatrix (n+1))
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    result M = PivotRowLoop.initial M := by
  rcases pivotTerminal_none_cases (DenseRatMatrix.decode M) ht with ⟨hz,hr⟩ | hp
  · have hf := noIndex M hr
    funext j
    simp [result,hz,PivotRowLoop.finished,hf,PivotRowLoop.initial,PivotRowLoop.state,
      Computability.encodeNat,Computability.encodeNum]
  · have hz := hp.ne'
    have hn := not_lt.mpr hp.le
    funext j
    by_cases hj : j = 29 <;>
      simp [result,hz,KS.W06.RationalSignClassifier.outputCode,hn,
        PivotRowLoop.initial,PivotRowLoop.state,Function.update,hj]

end KS.W17.PivotDecision

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionPorts
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def decisionProgram : Program 35 := liftPorts PivotDecision.program schurPorts

end KS.W17.FixedPSD

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

def unitTerminal : Program 35 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  KS.W19.TerminalVectorReplace.unitProgram
def sparseTerminal : Program 35 := compose (KS.W04.BinaryStackMoves.clearProgram 29)
  KS.W19.TerminalWitnessMachine.program

def terminalProgram : Program 35 := KS.W29.FixedBranch.branch unitTerminal sparseTerminal 23 terminalSelect

def terminalState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix n) (q : Fin n → ℚ) : Fin 35 → List Bool :=
  Function.update (matrixState saved M) 23 (KS.W12.RowDot.vectorTape q)

def finishTerminal : Program 35 := compose
  (KS.W04.CleanRationalCompare.clearListProgram 23 [31,26]) restoreAllProgram

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

def terminalRestoreProgram : Program 35 := compose terminalProgram finishTerminal

def afterDecision : Program 35 := KS.W29.FixedBranch.branch fullDescendProgram terminalRestoreProgram 23 afterDecisionSelect

def controllerBody : Program 35 := compose decisionProgram afterDecision

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotControllerLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def controllerProgram : Program 35 := KS.W29.FixedLoop.loop controllerBody controllerGuard

def controllerConfig (s : Fin 35 → List Bool) : Config 35 controllerProgram.states :=
  ⟨some controllerProgram.initial,s⟩

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalInputBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W07 KS.W01

theorem entry_length_le_payload {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    ratLength (DenseRatMatrix.decode M i j) ≤ (KS.W08.denseMatrixTape M).length := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n*n)))) =>
      Nat.zero_le (2*(encodeRat (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1
        (finProdFinEquiv.symm k).2)).length+1))
    (Finset.mem_univ (finProdFinEquiv (i,j)))
  rw [← KS.W08.denseMatrixTape_length] at h
  simp only [Equiv.symm_apply_apply] at h
  change ratLength (DenseRatMatrix.decode M i j) ≤ _
  dsimp only [ratLength]
  omega

theorem dimension_le_payload {n : ℕ} (M : DenseRatMatrix n) :
    n ≤ (KS.W08.denseMatrixTape M).length := by
  have h : n*n ≤ (KS.W08.denseMatrixTape M).length := by
    rw [KS.W08.denseMatrixTape_length]
    calc
      n*n = ∑ _k : Fin (n*n), (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun _ _ => by omega)
  exact (Nat.le_mul_self n).trans h

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotScannerBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PivotScannerBounds
open KS.W01 KS.W07 KS.W17 KS.W03.MachineCombinators
open KS.W19.TerminalWitnessMachine

theorem classify_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    PivotRowClassify.ticks M (W08.denseMatrixTape M).length j ≤
      2000*((W08.denseMatrixTape M).length+1)^3 := by
  let L := (W08.denseMatrixTape M).length
  have hn : n+1 ≤ L := dimension_le_payload M
  have hj : (Computability.encodeNat j.val).length ≤ L := (raw_length_le j.val).trans (by omega)
  have hd : (Computability.encodeNat (n+1)).length ≤ L := (raw_length_le (n+1)).trans hn
  have he : ratLength (DenseRatMatrix.decode M 0 j) ≤ L := entry_length_le_payload M 0 j
  have hc := classifier_code_length (DenseRatMatrix.decode M 0 j)
  have hp : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
  have hsq : (n+2)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hr : 1024*(n+2)^2*(L+1) ≤ 1024*(L+1)^3 := by
    calc
      1024*(n+2)^2*(L+1) ≤ 1024*(L+1)^2*(L+1) :=
        Nat.mul_le_mul_right (L+1) (Nat.mul_le_mul_left 1024 hsq)
      _ = _ := by ring
  change PivotRowClassify.ticks M L j ≤ 2000*(L+1)^3
  unfold PivotRowClassify.ticks
  omega

theorem row_body_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    PivotRowBody.ticks M (W08.denseMatrixTape M).length j ≤
      3000*((W08.denseMatrixTape M).length+1)^3 := by
  have h := classify_payload_bound M j
  have hn := dimension_le_payload M
  have hj := raw_length_le j.val
  have hp : (W08.denseMatrixTape M).length+1 ≤ ((W08.denseMatrixTape M).length+1)^3 :=
    Nat.le_self_pow (by decide) _
  unfold PivotRowBody.ticks
  omega

theorem entry_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) :
    PivotRowLoop.entryTicks M (W08.denseMatrixTape M).length a ≤
      3000*((W08.denseMatrixTape M).length+1)^3 := by
  unfold PivotRowLoop.entryTicks
  split
  · exact row_body_payload_bound M _
  · exact Nat.zero_le _

theorem loop_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) :
    PivotRowLoop.ticks M (W08.denseMatrixTape M).length a k ≤
      k*(1+3000*((W08.denseMatrixTape M).length+1)^3)+1 := by
  induction k generalizing a with
  | zero => simp [PivotRowLoop.ticks]
  | succ k ih =>
      have he := entry_payload_bound M a
      have ht := ih (a+1)
      rw [PivotRowLoop.ticks]
      split <;> nlinarith

theorem initialize_bound (n : ℕ) : PivotRowLoop.initializeTicks n ≤ 30*(n+1) := by
  have hn := raw_length_le n
  have hs := raw_length_le (n+1)
  have hm : max (Computability.encodeNat (n+1)).length 1 ≤ n+1 := max_le hs (by omega)
  unfold PivotRowLoop.initializeTicks SchurDimension.predecessorTicks
  omega

theorem finish_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    PivotRowLoop.finishTicks (PivotRowLoop.outcome M 1 n).index
      (PivotRowLoop.outcome M 1 n).remaining ≤ 13*((W08.denseMatrixTape M).length+1) := by
  have ho := PivotRowLoop.outcome_bounds M 1 n
  have hn := dimension_le_payload M
  have hi := raw_length_le (PivotRowLoop.outcome M 1 n).index
  unfold PivotRowLoop.finishTicks
  omega

theorem row_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    PivotDecision.rowTicks M (W08.denseMatrixTape M).length ≤
      10000*((W08.denseMatrixTape M).length+1)^4 := by
  let L := (W08.denseMatrixTape M).length
  have hn : n+1 ≤ L := dimension_le_payload M
  have hi := initialize_bound n
  have hl := loop_payload_bound M 1 n
  have hf := finish_payload_bound M
  have hp : 1 ≤ (L+1)^3 := Nat.one_le_pow' 3 L
  have hm : n*(1+3000*(L+1)^3) ≤ (L+1)*(3001*(L+1)^3) := by
    exact Nat.mul_le_mul (by omega) (by omega)
  have he : (L+1)*(3001*(L+1)^3) = 3001*(L+1)^4 := by ring
  rw [he] at hm
  have hp1 : L+1 ≤ (L+1)^4 := Nat.le_self_pow (by decide) _
  change PivotDecision.rowTicks M L ≤ 10000*(L+1)^4
  unfold PivotDecision.rowTicks
  change PivotRowLoop.ticks M L 1 n ≤ n*(1+3000*(L+1)^3)+1 at hl
  change PivotRowLoop.finishTicks (PivotRowLoop.outcome M 1 n).index
    (PivotRowLoop.outcome M 1 n).remaining ≤ 13*(L+1) at hf
  omega

theorem decision_payload_ticks {n : ℕ} (M : DenseRatMatrix (n+1)) :
    PivotDecision.ticks M (W08.denseMatrixTape M).length ≤
      100000000*((W08.denseMatrixTape M).length+1)^4 := by
  have hc := classify_payload_bound M 0
  have hr := row_payload_bound M
  have hp : ((W08.denseMatrixTape M).length+1)^3 ≤ ((W08.denseMatrixTape M).length+1)^4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : 1 ≤ ((W08.denseMatrixTape M).length+1)^4 :=
    Nat.one_le_pow' 4 (W08.denseMatrixTape M).length
  unfold PivotDecision.ticks
  split <;> omega

end KS.W23.PivotScannerBounds

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerTerminalBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

theorem unitTicks_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    unitTicks n ≤ 100*(localBits M+1) := by
  have hn := KS.W19.TerminalWitnessMachine.dimension_le_payload M
  have hl := KS.W19.TerminalWitnessMachine.raw_length_le (n+1)
  have hone : KS.W19.TerminalVectorReplace.oneFrame.length = 15 := by decide
  have hz := KS.W19.TerminalWitnessMachine.zero_payload_length (n+1)
  unfold unitTicks KS.W19.TerminalZeroVector.ticks
  rw [hone,hz]
  change _ ≤ 100*((KS.W08.denseMatrixTape M).length+1)
  omega

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_DenseFieldCounter
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.DenseFieldCounter
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.InputHeaderPrimitives

lemma base_decode_spec (d : ℕ) :
    RunSpec KS.W03.BinaryToUnary.program ![Computability.encodeNat d,[],[]]
      ![[],unary d,[]] (4*d+4*(Computability.encodeNat d).length+2) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat d) bits
    (by rw [KS.W19.bitsValue_encodeNat];omega)
  rw [KS.W03.BinaryToUnary.init_eq] at h
  simp only [KS.W19.bitsValue_encodeNat,unary] at h ⊢
  exact h

end CurrentKS.DenseFieldCounter

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotDescentBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PivotDescentBounds
open KS.W01 KS.W07 KS.W17.FixedPSD KS.W03.MachineCombinators
open KS.W19.TerminalWitnessMachine

theorem schur_payload_ticks {n : ℕ} (M : DenseRatMatrix (n+1)) :
    SchurTableMachine.totalTicks n (W08.denseMatrixTape M).length ≤
      2000000000000*((W08.denseMatrixTape M).length+1)^5 := by
  have hn := dimension_le_payload M
  exact (SchurTableMachine.totalTicks_mono (by omega : n ≤ (W08.denseMatrixTape M).length)
    le_rfl).trans (SchurTableMachine.inputLengthBudget_le_monomial _)

end KS.W23.PivotDescentBounds

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotReachableBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PivotReachableBounds
open KS.W07 KS.W17 KS.W17.FixedPSD KS.W19.TerminalWitnessMachine

def stepTicks {n : ℕ} (M : DenseRatMatrix (n+1)) : ℕ :=
  1+(PivotDecision.ticks M (localBits M)+(descentTicks M (localBits M)+1))

end KS.W23.PivotReachableBounds

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_reindex
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*} {encA : α → Word} {encB : β → Word}

def Realizes.lt {function other : α → ℚ}
    (realization : Realizes encA ratCode function) (comparison : Realizes encA ratCode other) :
    Realizes encA boolCode (fun input => decide (function input < other input)) :=
  ((comparison.le realization).ite
    (constant encA boolCode false) (constant encA boolCode true)).congr (by
      intro input
      by_cases bound : other input ≤ function input <;>
        simp [bound, not_lt_of_ge, lt_of_not_ge])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VectorRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α β γ : Type*}

def Realizes.zipWith {ea : α → Word} {eb : β → Word} {ec : γ → Word}
    {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β) :
    Realizes (prodCode (listCode ea) (listCode eb)) (listCode ec) (zipDefault f a b) :=
  let ctx := prodCode (listCode ea) (listCode eb)
  let ctxProjection := first ctx natCode
  let xs := ctxProjection.then (first (listCode ea) (listCode eb))
  let ys := ctxProjection.then (second (listCode ea) (listCode eb))
  let idx := second ctx natCode
  let xi := (idx.both xs).then (getD ea a)
  let yi := (idx.both ys).then (getD eb b)
  let each := (xi.both yi).then r
  ((identity ctx).both ((first (listCode ea) (listCode eb)).then (lengthList ea))).then each.tabulate

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MatrixStructureRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixEntry : Realizes (prodCode matrixCode (prodCode natCode natCode)) ratCode
    (fun p => (p.1.getD p.2.1 []).getD p.2.2 0) :=
  let M := first matrixCode (prodCode natCode natCode)
  let ij := second matrixCode (prodCode natCode natCode)
  let i := ij.then (first natCode natCode)
  let j := ij.then (second natCode natCode)
  (j.both ((i.both M).then (getD vectorCode []))).then (getD ratCode 0)

variable {α : Type*}

def transposeMatrix : Realizes matrixCode matrixCode transposeData :=
  let ctx := prodCode matrixCode natCode
  let p := first ctx natCode
  let M := p.then (first matrixCode natCode)
  let i := p.then (second matrixCode natCode)
  let j := second ctx natCode
  let entry := (M.both (j.both i)).then matrixEntry
  let n := lengthList vectorCode
  (((identity matrixCode).both n).both n).then entry.matrixTabulate

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PSDCleanRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.PSDCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07 KS.W17 KS.W17.FixedPSD
open CleanRoutine

def decode : Program 35 := KS.W11.FrameWireCodec.unframeProgram ⟨![0,26,34],by decide⟩
def install : Program 35 := CleanRoutine.transfer 0 34 31
def extract : Program 35 := CleanRoutine.transfer 23 34 0
def program : Program 35 := compose decode (compose install (compose controllerProgram extract))

lemma decode_spec (a : Datum) : RunSpec decode (io (input a))
    (parsed (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2))
    (3*(Computability.encodeNat a.1).length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec
    (⟨![0,26,34],by decide⟩ : Fin 3 ↪ Fin 35) (fun _ => [])
    (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> fin_cases j <;> rfl)

lemma install_spec (a : Datum) : RunSpec install
    (parsed (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2)) (matrixState [] a.2)
    (2*(KS.W08.denseMatrixTape a.2).length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin 35) 34 31 (by decide) (by decide) (by decide)
    (parsed (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2)) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [parsed,matrixState,state,Function.update]

lemma extract_spec {n : ℕ} (v : Option (Fin n → ℚ)) : RunSpec extract
    (witnessState v) (io (v.elim [] KS.W12.RowDot.vectorTape))
    (2*(v.elim [] KS.W12.RowDot.vectorTape).length+2) := by
  have h := CleanRoutine.transfer_spec (23 : Fin 35) 34 0 (by decide) (by decide) (by decide)
    (witnessState v) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [witnessState,state,io,Function.update]

end CurrentKS.PSDCleanRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RatFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W29.FixedSequential KS.W03.MachineCombinators

def wordTail : Realizes (id : Word → Word) id List.tail where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W23.LiteralProgram.pop 0
    spec := fun w => by
      have h := KS.W23.LiteralProgram.pop_spec (0 : Fin 1) (io w)
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
      funext j;fin_cases j;rfl }

abbrev numFieldsCode := prodCode binaryNatCode (fun n => KS.W01.encodeNat n)

def ratFields : Realizes ratCode numFieldsCode
    (fun q => (KS.W01.intPayload q.num,q.den)) :=
  (wordTail.reindex ratCode ratCode (fun _ => rfl)).changeOutput numFieldsCode
    (fun q => (KS.W01.intPayload q.num,q.den)) (by
      intro q
      change (KS.W01.encodeRat q).tail=_
      unfold KS.W01.encodeRat numFieldsCode prodCode PairRoutine.pair
      dsimp only
      cases q.num <;> rfl)

def ratNumBinary : Realizes ratCode binaryNatCode (fun q => KS.W01.intPayload q.num) :=
  ratFields.then (first binaryNatCode (fun n => KS.W01.encodeNat n))

def binaryToNat : Realizes binaryNatCode natCode id where
  cost := fun n => 6*n+4*(binaryNatCode n).length+4
  routine := {
    scratch := 2
    program := compose KS.W03.BinaryToUnary.program (CleanRoutine.transfer 1 2 0)
    spec := fun n => by
      have hd := DenseFieldCounter.base_decode_spec n
      have ht := PairRoutine.take_first (natCode n)
      have h := hd.compose ht
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
      · funext j;fin_cases j <;> rfl
      · simp only [natCode,binaryNatCode,List.length_replicate];omega }

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix
open scoped BigOperators

def rawEntry : Realizes varEntryCode ratCode
    (fun a => a.1.1.2.getD (a.2+a.1.1.1.1*a.1.2) 0) :=
  ((varEntryJ.nadd ((varEntryVars.then variablesN).nmul varEntryI)).both
    (varEntryVars.then variableValues)).then (getD ratCode 0)

def raw : Realizes variablesCode matrixCode
    (fun p => (List.range p.1.1).map (fun i =>
      (List.range p.1.1).map (fun j => p.2.getD (j+p.1.1*i) 0))) :=
  (((identity variablesCode).both variablesN).both variablesN).then rawEntry.matrixTabulate

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil parameters. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

abbrev paramsN : Realizes paramsCode natCode (fun p => p.graph.n) := paramsGraph.then numVertices

def paramsField (k : ℕ) := ((constant paramsCode natCode k).both paramsFields).then (getD ratCode 0)
abbrev paramsS : Realizes paramsCode ratCode Params.s := paramsField 0
abbrev paramsK : Realizes paramsCode ratCode Params.κ := paramsField 1
abbrev paramsT : Realizes paramsCode ratCode Params.t := paramsField 2
abbrev paramsQ : Realizes paramsCode ratCode Params.q := paramsField 3
abbrev paramsE : Realizes paramsCode ratCode Params.ε := paramsField 4
abbrev paramsDim := (paramsN.both paramsM).then dimensionProgram

abbrev pointN : Realizes pointCode natCode (fun a => a.p.graph.n) := pointParams.then paramsN
abbrev pointS : Realizes pointCode ratCode (fun a => a.p.s) := pointParams.then paramsS
abbrev pointK : Realizes pointCode ratCode (fun a => a.p.κ) := pointParams.then paramsK
abbrev pointT : Realizes pointCode ratCode (fun a => a.p.t) := pointParams.then paramsT
abbrev pointQ : Realizes pointCode ratCode (fun a => a.p.q) := pointParams.then paramsQ
abbrev pointE : Realizes pointCode ratCode (fun a => a.p.ε) := pointParams.then paramsE
def pointParser : Realizes (prodCode paramsCode vectorCode) pointCode parsePoint :=
  let a := first paramsCode vectorCode
  let vs := second paramsCode vectorCode
  let base := first (prodCode paramsCode vectorCode) natCode
  let idx := second (prodCode paramsCode vectorCode) natCode
  let val := (idx.both (base.then vs)).then (getD ratCode 0)
  (a.both ((((identity (prodCode paramsCode vectorCode)).both (a.then paramsDim)).then val.tabulate))).changeOutput
    pointCode parsePoint (by
      intro a
      change prodCode paramsCode vectorCode (a.1,(List.range _).map _)=
        prodCode paramsCode vectorCode (a.1,List.ofFn _)
      rw [range_map_fin]
      rfl)

variable {α : Type*} {ea : α → Word} {p : α → Point}
def coordinate (rp : Realizes ea pointCode p)
    (i : (a : α) → Fin (dimension (p a).p.graph.n (p a).p.graph.m))
    (ri : Realizes ea natCode (fun a => (i a).val)) :
    Realizes ea ratCode (fun a => (p a).v (i a)) :=
  ((ri.both (rp.then pointVector)).then (getD ratCode 0)).congr
    (fun a => getD_ofFn (p a).v (i a) 0)

def rawPoint : Realizes pointCode matrixObjectCode
    (fun a => ⟨a.p.graph.n,rawMatrix a.v⟩) :=
  (pointN.both ((((pointN.both pointM).both pointVector).then raw))).changeOutput
    matrixObjectCode (fun a => ⟨a.p.graph.n,rawMatrix a.v⟩) (by
      intro a
      change prodCode natCode matrixCode (a.p.graph.n,
        (List.range a.p.graph.n).map (fun i => (List.range a.p.graph.n).map
          (fun j => (List.ofFn a.v).getD (j+a.p.graph.n*i) 0)))=_
      rw [raw_data]
      rfl)
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_PointPrograms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α β : Type*} {ea : α → Word} {eb : β → Word}

def select3 {i : α → Fin 3} (ri : Realizes ea natCode (fun a => (i a).val))
    {f g h : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g)
    (t : Realizes ea ratCode h) : Realizes ea ratCode (fun a => ![f a,g a,h a] (i a)) :=
  ((ri.both (r.cons (s.cons (t.then (singleton ratCode))))).then (getD ratCode 0)).congr (by
    intro a
    exact getD_ofFn ![f a,g a,h a] (i a) 0)

def select7 {i : α → Fin 7} (ri : Realizes ea natCode (fun a => (i a).val))
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : α → ℚ}
    (r₀ : Realizes ea ratCode f₀) (r₁ : Realizes ea ratCode f₁) (r₂ : Realizes ea ratCode f₂)
    (r₃ : Realizes ea ratCode f₃) (r₄ : Realizes ea ratCode f₄) (r₅ : Realizes ea ratCode f₅)
    (r₆ : Realizes ea ratCode f₆) :
    Realizes ea ratCode (fun a => ![f₀ a,f₁ a,f₂ a,f₃ a,f₄ a,f₅ a,f₆ a] (i a)) :=
  ((ri.both (r₀.cons (r₁.cons (r₂.cons (r₃.cons (r₄.cons (r₅.cons
    (r₆.then (singleton ratCode))))))))).then (getD ratCode 0)).congr (by
      intro a
      exact getD_ofFn ![f₀ a,f₁ a,f₂ a,f₃ a,f₄ a,f₅ a,f₆ a] (i a) 0)
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {a : α → Point}

def edgeCoord (p : Fin 3) (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea ratCode (fun b => (a b).v (edgeIndex p (e b))) :=
  let n := r.then pointN
  let m := r.then pointM
  coordinate r (fun b => edgeIndex p (e b))
    ((n.nmul n).nadd ((n.nmul (n.nmul n)).nadd (re.nadd (m.nmul (constant ea natCode p.val)))))

def flowCoord (p : Fin 2) (r : Realizes ea pointCode a)
    (v : (b : α) → Fin (a b).p.graph.n) (e : (b : α) → Fin (a b).p.graph.m)
    (rv : Realizes ea natCode (fun b => (v b).val)) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea ratCode (fun b => (a b).v (flowIndex p (v b) (e b))) :=
  let n := r.then pointN
  let m := r.then pointM
  coordinate r (fun b => flowIndex p (v b) (e b))
    ((n.nmul n).nadd ((n.nmul (n.nmul n)).nadd
      (((constant ea natCode 3).nmul m).nadd
        ((re.nadd (m.nmul rv)).nadd ((n.nmul m).nmul (constant ea natCode p.val))))))

def storedU (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea ratCode (fun b => (a b).p.u (e b)) :=
  ((re.both (r.then pointU)).then (getD ratCode 0)).congr (fun b => getD_ofFn _ (e b) 0)

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_ScalarConstraintRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar constraint realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

abbrev esK := esPoint.then pointK
abbrev esT := esPoint.then pointT

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack

abbrev scalarCount := (pointN.nmul (pointN.nmul pointN)).nadd
  (((constant pointCode natCode 7).nmul pointM).nadd
    (((constant pointCode natCode 3).nmul (pointN.nmul pointM)).nadd
      ((pointN.nmul pointN).nadd (constant pointCode natCode 1))))

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
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

abbrev graphDim := (numVertices.both numEdges).then dimensionProgram

def graphZeros : Realizes graphCode vectorCode (fun G => List.ofFn (0 : Fin (dimension G.n G.m) → ℚ)) :=
  (((constant graphCode ratCode 0).both graphDim).then (replicateList ratCode)).congr
    (by
      intro G
      change List.replicate (dimension G.n G.m) 0 = List.ofFn (fun _ : Fin (dimension G.n G.m) => (0 : ℚ))
      rw [List.ofFn_const])
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end


